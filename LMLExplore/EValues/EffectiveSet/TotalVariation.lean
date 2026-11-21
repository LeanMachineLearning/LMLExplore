/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.EValues.BipolarRate.Basic
public import LMLExplore.EValues.EffectiveSet.Basic
public import Mathlib.MeasureTheory.Measure.TotalVariation.Defs
public import Mathlib.Probability.ProductMeasure

import LMLExplore.MeasureTheory.Measure.TotalVariation.Basic
import LMLExplore.MeasureTheory.Measure.TotalVariation.Pi
import TauCeti.MeasureTheory.Measure.TotalVariation.Basic

/-!
# Nulls dense in total variation

The effective null `effectiveSet S` of a null `S` is closed under setwise convergence
(`ProbabilityTheory.mem_effectiveSet_of_measure_le_liminf`), hence in total variation. So every
limit in total variation of members of a null of probability measures belongs to its effective
null, and no e-variable for `S` has expectation above `1` under it. A null that is dense in
total variation among the probability measures therefore has the e-variables of the null of all
laws: e-variables cannot tell it apart from the null of all laws, and they have no power.

* **One observation.** If every point mass `Measure.dirac x` is a limit in total variation of
  members of `S`, the e-variables for `S` are the measurable functions bounded by `1`
  everywhere. This applies to the laws of independent sequences, indexed by a countable type,
  with marginals in such a null, on a space with measurable singletons: on a given sequence, the
  marginals can be chosen to miss masses of arbitrarily small sum.
* **Finitely many i.i.d. observations.** Total variation is subadditive over products
  (`MeasureTheory.etvDist_pi_le_sum`), so if a probability measure `Q` is a limit in total
  variation of members of `S`, then `Q ^ n` is a limit of members of `S ^ n` for every `n`, and
  lies in the effective null of the null `sampleNull S n` of `n` i.i.d. observations. If this
  holds for every `Q`, an `n`-sample function is an e-variable for the i.i.d. laws of `S` exactly
  when it is one for the i.i.d. laws of all probability measures. Under the i.i.d. law of such a
  `Q`, the maximal expected logarithm `maxLogGrowth Q S n` of an `n`-sample e-variable and the
  bipolar rate `bipolarRate Q S` vanish, and a test of level `α` for the i.i.d. laws of `S` has
  power at most `α`.

The null on `ℝ` of the laws with mean `0` and a finite, positive variance
(`ProbabilityTheory.meanZeroPosVarNull`) is the motivating instance; this is the form for
e-variables of the theorem of Bahadur and Savage [BS56].

## Main statements

* `ProbabilityTheory.mem_effectiveSet_of_forall_exists_etvDist_lt`: the effective null is closed
  in total variation.
* `ProbabilityTheory.isEVar_iff_of_forall_exists_etvDist_dirac_lt`: if every point mass is a limit
  in total variation of members of `S`, the e-variables for `S` are the measurable functions
  bounded by `1`.
* `ProbabilityTheory.isEVar_infinitePi_iff_of_forall_exists_etvDist_dirac_lt`: the same for the
  laws of independent sequences with marginals in `S`.
* `ProbabilityTheory.pi_mem_effectiveSet_of_forall_exists_etvDist_lt`,
  `ProbabilityTheory.pi_mem_effectiveSet_sampleNull_of_forall_exists_etvDist_lt`: a limit `Q` in
  total variation of members of `S` has `Q ^ ι` in the effective null of the i.i.d. null, for every
  finite `ι`, and in particular `Q ^ n` in the effective null of `sampleNull S n`.
* `ProbabilityTheory.isEVar_pi_iff_of_forall_exists_etvDist_lt`: a null dense in total variation
  has, for every finite number of i.i.d. observations, the e-variables of the null of all laws.
* `ProbabilityTheory.lintegral_pi_le_of_forall_exists_etvDist_lt`,
  `ProbabilityTheory.maxLogGrowth_eq_zero_of_forall_exists_etvDist_lt`,
  `ProbabilityTheory.bipolarRate_eq_zero_of_forall_exists_etvDist_lt`: against such a `Q`, tests
  have no power and evidence does not grow.

## Implementation notes

Membership in the effective null is derived from its closure under setwise convergence, in the
form `ProbabilityTheory.mem_effectiveSet_of_measure_le_liminf`, which handles unbounded
e-variables by monotone convergence. Total variation enters only through the eventwise bound
`μ s ≤ ν s + etvDist μ ν` (`MeasureTheory.measure_le_add_etvDist`) and its subadditivity over
products.

The results are those of [EVR26, Note 22]. The proofs are rewritten from the Lean proofs in
`EValuesResearch/Results/PowerlessNulls.lean` (commit `dd4072f`) of the paper project
`RemyDegenne/evalues_research`, which proves the corollary directly, by common minorants and
truncation, and the statements for one observation and for sequences through the masses
`⨆ P ∈ S, P {x}`; here all of them go through the closure of the effective null. [BS56] is cited
for the theorem of which this is the form for e-variables; its proofs are not used.

## References

* [BS56] R. R. Bahadur and L. J. Savage, *The nonexistence of certain statistical procedures in
  nonparametric problems*, Ann. Math. Statist. 27 (1956).
* [EVR26] *Answers to open questions in e-values and anytime-valid inference*, Note 22, and the
  Lean library `EValuesResearch` of github.com/RemyDegenne/evalues_research, 2026.
-/

public section

open MeasureTheory Filter Set InformationTheory

open scoped ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {S : Set (Measure Ω)} {μ : Measure Ω}

/-! ### Closure in total variation -/

/-- **The effective null is closed in total variation**: a measure that is a limit in total
variation of members of the effective null of `S` belongs to it. -/
theorem mem_effectiveSet_of_forall_exists_etvDist_lt
    (h : ∀ ε > 0, ∃ ν ∈ effectiveSet S, etvDist ν μ < ε) : μ ∈ effectiveSet S := by
  -- The members of the effective null, along the filter of their distance to `μ` tending to `0`.
  set f : effectiveSet S → ℝ≥0∞ := fun ν ↦ etvDist (ν : Measure Ω) μ
  have : (Filter.comap f (𝓝 0)).NeBot :=
    (ENNReal.nhds_zero_basis.comap f).neBot_iff.2 fun {ε} hε ↦
      let ⟨ν, hν, hνμ⟩ := h ε hε
      ⟨⟨ν, hν⟩, hνμ⟩
  refine mem_effectiveSet_of_measure_le_liminf (l := Filter.comap f (𝓝 0)) (μs := Subtype.val)
    (.of_forall fun ν ↦ ν.2) fun s hs ↦ ENNReal.le_of_forall_pos_le_add fun ε hε _ ↦ ?_
  have hev : ∀ᶠ ν : effectiveSet S in Filter.comap f (𝓝 0), μ s - ε ≤ (ν : Measure Ω) s := by
    filter_upwards [tendsto_comap.eventually (gt_mem_nhds (ENNReal.coe_pos.2 hε))] with ν hν
    exact tsub_le_iff_right.2 (measure_le_add_of_etvDist_le hs hν.le)
  exact tsub_le_iff_right.1 (le_liminf_of_le (by isBoundedDefault) hev)

/-- A limit in total variation of members of a null `S` belongs to the effective null of `S`. -/
private lemma mem_effectiveSet_of_forall_exists_mem_etvDist_lt
    (h : ∀ ε > 0, ∃ P ∈ S, etvDist P μ < ε) : μ ∈ effectiveSet S :=
  mem_effectiveSet_of_forall_exists_etvDist_lt fun ε hε ↦
    let ⟨P, hP, hPμ⟩ := h ε hε
    ⟨P, subset_effectiveSet hP, hPμ⟩

/-! ### One observation and independent sequences -/

/-- **One observation.** If every point mass is a limit in total variation of members of a null
`S` of measures of mass at most `1` (for instance probability measures), the e-variables for `S`
are the measurable functions bounded by `1` everywhere. -/
theorem isEVar_iff_of_forall_exists_etvDist_dirac_lt (hS : ∀ P ∈ S, P univ ≤ 1)
    (hS_dirac : ∀ x : Ω, ∀ ε > 0, ∃ P ∈ S, etvDist P (Measure.dirac x) < ε)
    {X : Ω → ℝ≥0∞} :
    IsEVar X S ↔ Measurable X ∧ ∀ x, X x ≤ 1 := by
  refine ⟨fun hX ↦ ⟨hX.measurable, fun x ↦ ?_⟩, fun h ↦ ⟨h.1, fun P hP ↦ ?_⟩⟩
  · have hx : Measure.dirac x ∈ effectiveSet S :=
      mem_effectiveSet_of_forall_exists_mem_etvDist_lt (hS_dirac x)
    simpa [lintegral_dirac' x hX.measurable] using hx X hX
  · calc ∫⁻ ω, X ω ∂P ≤ ∫⁻ _, 1 ∂P := lintegral_mono h.2
    _ = P univ := lintegral_one
    _ ≤ 1 := hS P hP

variable {𝓧 : Type*} {m𝓧 : MeasurableSpace 𝓧} {S : Set (Measure 𝓧)}

/-- If every point mass is a limit in total variation of members of a null `S` of probability
measures, so is every point mass on `ι → 𝓧`, for a countable `ι`, of laws of independent
sequences with marginals in `S`: on the given sequence `x`, the marginals can be chosen so that
the masses they miss have a small sum. -/
private lemma exists_infinitePi_etvDist_dirac_lt {ι : Type*} [Countable ι]
    [MeasurableSingletonClass 𝓧] (hS : ∀ P ∈ S, IsProbabilityMeasure P)
    (hS_dirac : ∀ x : 𝓧, ∀ ε > 0, ∃ P ∈ S, etvDist P (Measure.dirac x) < ε) (x : ι → 𝓧)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ P ∈ Measure.infinitePi '' {P : ι → Measure 𝓧 | ∀ i, P i ∈ S},
      etvDist P (Measure.dirac x) < ε := by
  obtain ⟨δ, hδ0, hδ⟩ := ENNReal.exists_pos_sum_of_countable (ENNReal.half_pos hε.ne').ne' ι
  -- For each `i`, a member of `S` that misses a mass at most `δ i` of the point `x i`.
  have hchoose (i : ι) : ∃ P ∈ S, P {x i}ᶜ < δ i := by
    obtain ⟨P, hP, hPx⟩ := hS_dirac (x i) (2 * δ i) (by simpa using hδ0 i)
    have := hS P hP
    refine ⟨P, hP, ?_⟩
    rw [etvDist_comm, etvDist_dirac_left] at hPx
    rw [prob_compl_eq_one_sub (measurableSet_singleton _)]
    exact (ENNReal.mul_lt_mul_iff_right two_ne_zero ENNReal.ofNat_ne_top).1 hPx
  choose P hPS hPx using hchoose
  have := fun i ↦ hS _ (hPS i)
  refine ⟨Measure.infinitePi P, ⟨P, hPS, rfl⟩, ?_⟩
  have hcompl : Measure.infinitePi P {x}ᶜ < ε / 2 := by
    calc Measure.infinitePi P {x}ᶜ
    _ ≤ Measure.infinitePi P (⋃ i, Function.eval i ⁻¹' {x i}ᶜ) := by
      refine measure_mono fun y hy ↦ ?_
      obtain ⟨i, hi⟩ := Function.ne_iff.1 hy
      exact mem_iUnion.2 ⟨i, hi⟩
    _ ≤ ∑' i, Measure.infinitePi P (Function.eval i ⁻¹' {x i}ᶜ) := measure_iUnion_le _
    _ = ∑' i, P i {x i}ᶜ := by
      congr 1 with i
      exact (measurePreserving_eval_infinitePi P i).measure_preimage
        (measurableSet_singleton _).compl.nullMeasurableSet
    _ ≤ ∑' i, (δ i : ℝ≥0∞) := by gcongr with i; exact (hPx i).le
    _ < ε / 2 := hδ
  rw [etvDist_comm, etvDist_dirac_left, mul_comm]
  refine (ENNReal.lt_div_iff_mul_lt (.inl two_ne_zero) (.inl ENNReal.ofNat_ne_top)).1
    (lt_of_le_of_lt ?_ hcompl)
  rw [tsub_le_iff_left, ← measure_univ (μ := Measure.infinitePi P)]
  exact measure_univ_le_add_compl _

/-- **Independent sequences.** If every point mass is a limit in total variation of members of a
null `S` of probability measures, on a space with measurable singletons, the e-variables for the
laws of the independent sequences indexed by a countable `ι` with marginals in `S` are the
measurable functions bounded by `1` everywhere. -/
theorem isEVar_infinitePi_iff_of_forall_exists_etvDist_dirac_lt {ι : Type*} [Countable ι]
    [MeasurableSingletonClass 𝓧] (hS : ∀ P ∈ S, IsProbabilityMeasure P)
    (hS_dirac : ∀ x : 𝓧, ∀ ε > 0, ∃ P ∈ S, etvDist P (Measure.dirac x) < ε)
    {X : (ι → 𝓧) → ℝ≥0∞} :
    IsEVar X (Measure.infinitePi '' {P : ι → Measure 𝓧 | ∀ i, P i ∈ S}) ↔
      Measurable X ∧ ∀ x, X x ≤ 1 := by
  refine isEVar_iff_of_forall_exists_etvDist_dirac_lt ?_
    fun x _ hε ↦ exists_infinitePi_etvDist_dirac_lt hS hS_dirac x hε
  rintro _ ⟨P, hP, rfl⟩
  have := fun i ↦ hS _ (hP i)
  exact prob_le_one

/-! ### Finitely many i.i.d. observations -/

variable {ι : Type*} [Fintype ι] {Q : Measure 𝓧}

/-- If `Q` is a limit in total variation of members of a null `S` of probability measures, then
`Q ^ ι` is a limit in total variation of the products `P ^ ι` of members of `S`. -/
private lemma exists_etvDist_pi_lt (hS : ∀ P ∈ S, IsProbabilityMeasure P)
    [IsProbabilityMeasure Q] (hQ : ∀ ε > 0, ∃ P ∈ S, etvDist P Q < ε) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ P ∈ S, etvDist (Measure.pi fun _ : ι ↦ P) (Measure.pi fun _ : ι ↦ Q) < ε := by
  obtain ⟨P, hP, hPQ⟩ := hQ (ε / Fintype.card ι)
    (ENNReal.div_pos hε.ne' (ENNReal.natCast_ne_top _))
  have := hS P hP
  refine ⟨P, hP, (etvDist_pi_const_le_card_mul P Q).trans_lt ?_⟩
  rw [mul_comm]
  exact (ENNReal.lt_div_iff_mul_lt (.inr (etvDist_ne_top _ _))
    (.inl (ENNReal.natCast_ne_top _))).1 hPQ

/-- **I.i.d. observations of a limit in total variation.** If a probability measure `Q` is a limit
in total variation of members of a null `S` of probability measures, then for every finite `ι` the
product `Q ^ ι` belongs to the effective null of the i.i.d. null `{P ^ ι | P ∈ S}`: no e-variable
for the i.i.d. laws of `S` has expectation above `1` under the i.i.d. law of `Q`. -/
theorem pi_mem_effectiveSet_of_forall_exists_etvDist_lt (hS : ∀ P ∈ S, IsProbabilityMeasure P)
    (hQ : ∀ ε > 0, ∃ P ∈ S, etvDist P Q < ε) :
    Measure.pi (fun _ : ι ↦ Q) ∈ effectiveSet ((fun P ↦ Measure.pi fun _ : ι ↦ P) '' S) := by
  have := isProbabilityMeasure_of_forall_exists_etvDist_lt hS hQ
  refine mem_effectiveSet_of_forall_exists_mem_etvDist_lt fun ε hε ↦ ?_
  obtain ⟨P, hP, hPQ⟩ := exists_etvDist_pi_lt (ι := ι) hS hQ hε
  exact ⟨_, ⟨P, hP, rfl⟩, hPQ⟩

/-- **`n` i.i.d. observations of a limit in total variation.** If a probability measure `Q` is a
limit in total variation of members of a null `S` of probability measures, then for every `n` the
product `Q ^ n` belongs to the effective null of the null `sampleNull S n` of `n` i.i.d.
observations. This is `pi_mem_effectiveSet_of_forall_exists_etvDist_lt` for `ι = Fin n`. -/
theorem pi_mem_effectiveSet_sampleNull_of_forall_exists_etvDist_lt
    (hS : ∀ P ∈ S, IsProbabilityMeasure P) (hQ : ∀ ε > 0, ∃ P ∈ S, etvDist P Q < ε) (n : ℕ) :
    Measure.pi (fun _ : Fin n ↦ Q) ∈ effectiveSet (sampleNull S n) :=
  sampleNull_def S n ▸ pi_mem_effectiveSet_of_forall_exists_etvDist_lt hS hQ

/-- **A null dense in total variation has the e-variables of all laws.** If every probability
measure is a limit in total variation of members of a null `S` of probability measures, then for
every finite set `ι` of i.i.d. observations, a function is an e-variable for the products `P ^ ι`
of the members of `S` exactly when it is one for the products of all probability measures. -/
theorem isEVar_pi_iff_of_forall_exists_etvDist_lt (hS : ∀ P ∈ S, IsProbabilityMeasure P)
    (hdense : ∀ Q : Measure 𝓧, IsProbabilityMeasure Q → ∀ ε > 0, ∃ P ∈ S, etvDist P Q < ε)
    {X : (ι → 𝓧) → ℝ≥0∞} :
    IsEVar X ((fun P ↦ Measure.pi fun _ : ι ↦ P) '' S) ↔
      IsEVar X ((fun P ↦ Measure.pi fun _ : ι ↦ P) '' {P | IsProbabilityMeasure P}) := by
  refine ⟨fun hX ↦ ⟨hX.measurable, ?_⟩, fun hX ↦ hX.anti_set (image_mono fun P hP ↦ hS P hP)⟩
  rintro _ ⟨Q, hQ, rfl⟩
  have : IsProbabilityMeasure Q := hQ
  exact pi_mem_effectiveSet_of_forall_exists_etvDist_lt hS (hdense Q hQ) X hX

/-- **No power against a limit in total variation.** If a probability measure `Q` is a limit in
total variation of members of a null `S` of probability measures, a test of level `α` for the
i.i.d. laws `P ^ ι` of the members of `S` has power at most `α` against the i.i.d. law of `Q`. -/
theorem lintegral_pi_le_of_forall_exists_etvDist_lt (hS : ∀ P ∈ S, IsProbabilityMeasure P)
    (hQ : ∀ ε > 0, ∃ P ∈ S, etvDist P Q < ε) {φ : (ι → 𝓧) → ℝ≥0∞} {α : ℝ≥0∞}
    (hφ : IsTest φ ((fun P ↦ Measure.pi fun _ : ι ↦ P) '' S) α) :
    ∫⁻ x, φ x ∂(Measure.pi fun _ : ι ↦ Q) ≤ α :=
  (isTest_effectiveSet_iff.2 hφ).lintegral_le _
    (pi_mem_effectiveSet_of_forall_exists_etvDist_lt hS hQ)

/-- **No growth against a limit in total variation.** If a probability measure `Q` is a limit in
total variation of members of a null `S` of probability measures, the maximal expected logarithm
under `Q ^ n` of an `n`-sample e-variable for the i.i.d. laws of `S` is `0`. -/
theorem maxLogGrowth_eq_zero_of_forall_exists_etvDist_lt (hS : ∀ P ∈ S, IsProbabilityMeasure P)
    (hQ : ∀ ε > 0, ∃ P ∈ S, etvDist P Q < ε) (n : ℕ) :
    maxLogGrowth Q S n = 0 := by
  have := isProbabilityMeasure_of_forall_exists_etvDist_lt hS hQ
  refine le_antisymm ?_ (maxLogGrowth_nonneg _ (fun P hP ↦ (hS P hP).measure_univ.le) _)
  rw [maxLogGrowth_def]
  exact (maxEPower_eq_zero_of_mem_effectiveSet
    (measure_univ_le_one_of_mem_sampleNull (fun P hP ↦ (hS P hP).measure_univ.le) n)
    (pi_mem_effectiveSet_sampleNull_of_forall_exists_etvDist_lt hS hQ n)).le

/-- **The bipolar rate against a limit in total variation is zero.** If a probability measure `Q`
is a limit in total variation of members of a null `S` of probability measures, the optimal growth
rate `bipolarRate Q S` of the evidence against the i.i.d. laws of `S` under the i.i.d. law of `Q`
is `0`. -/
theorem bipolarRate_eq_zero_of_forall_exists_etvDist_lt (hS : ∀ P ∈ S, IsProbabilityMeasure P)
    (hQ : ∀ ε > 0, ∃ P ∈ S, etvDist P Q < ε) :
    bipolarRate Q S = 0 := by
  simp [bipolarRate_def, maxLogGrowth_eq_zero_of_forall_exists_etvDist_lt hS hQ]

end ProbabilityTheory
