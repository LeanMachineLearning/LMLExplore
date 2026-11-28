/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.EValues.EProcess.LevelStoppingTime
public import LMLExplore.EValues.KLInf
public import LMLExplore.EValues.Null.Basic
public import LMLExplore.EValues.TestSupermartingale.SequentialNull
public import Mathlib.Probability.Process.HittingTime
import LMLExplore.EValues.BipolarRate.Numeraire.Test
import LMLExplore.EValues.EffectiveSet.Basic
import LMLExplore.EValues.TestSupermartingale.Betting
import LMLExplore.MeasureTheory.Integral.Lebesgue.Countable
import LMLExplore.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Probability.Independence.InfinitePi

/-!
# Test supermartingales see the effective null, and their tests are slow

Let `S₁` be a set of probability measures on `𝓧`, each of which charges every point of `𝓧`, and
let `M` be a test supermartingale for the i.i.d. null `iidNull S₁`, in the filtration
`Filtration.piLT` of the past observations. Every past has positive probability under every
member of the null, so `M` satisfies the one-step condition
`∫⁻ y, M (n + 1) (update ω n y) ∂P ≤ M n ω` at every past `ω` and for every `P ∈ S₁`
(`ProbabilityTheory.IsENNSupermartingale.lintegral_update_le_of_infinitePi`). A bound on integrals
that holds on `S₁` holds on its effective null `effectiveSet S₁`, the measures under which every
e-variable for `S₁` has mean at most `1` (`ProbabilityTheory.lintegral_le_of_mem_effectiveSet`).
So `M` satisfies the one-step condition for the members of the effective null, and it is a test
supermartingale for the sequential null of the probability measures of the effective null: the
laws under which every observation, given the past, has a law in it. The effective null contains
the mixtures of members of `S₁` and is closed under limits: on a countable alphabet, it contains
the probability measures whose masses `Q₁ {x}` are pointwise limits of those of mixtures of
members of `S₁`, by Fatou's lemma for sums. In particular `M` is a test supermartingale for the
i.i.d. null of the convex hull of `S₁` and for the i.i.d. law of every such limit, and the test
that rejects when `M` reaches `α⁻¹` has level `α` there: it has no power inside the closed convex
hull of the null [EVR26, Note 32, Statement 1].

Without the hypothesis that every member charges every point, this fails: for the null of the two
point masses on `Bool`, some test martingale tends to `∞` almost surely under fair coins, a mixture
of them (`ProbabilityTheory.exists_isTestMartingale_dirac_tendsto_top`).

The expected number of observations of these tests is governed by the largest expected logarithm
`a₁ = maxEPower Q₁ S₁` of an e-variable of one observation, rather than by the bipolar rate. Every
level-`α` sequential test `τ` for the independent null `indepNull S₁` (the laws of independent
observations with laws in `S₁`) has `log (1/α) ≤ a₁ 𝔼[τ]` under the i.i.d. law of a probability
measure `Q₁` (`ProbabilityTheory.toENNReal_log_inv_div_maxEPower_le_lintegral_of_indepNull`). Since
the test
supermartingales of a null whose members charge every point are test supermartingales for its
sequential null, which contains its independent null, their tests need at least
`log (1/α) / a₁` observations in expectation [EVR26, Note 32, Statement 1]. For a null that is not
convex, the bipolar rate `d` can be much larger than `a₁`, and the tests of other e-processes need
only `log (1/α) / d` observations to first order
(`ProbabilityTheory.exists_isLevelStoppingTime_limsup_lintegral_div_log_le`).

## Main statements

* `ProbabilityTheory.isTestSupermartingale_sequentialNull_effectiveSet_of_iidNull`: a test
  supermartingale for the i.i.d. null of laws that charge every point is a test supermartingale
  for the sequential null of the probability measures of its effective null.
* `ProbabilityTheory.isLevelStoppingTime_hittingAfter_infinitePi_of_mem_effectiveSet`: its test
  of level `α` has level `α` for the i.i.d. law of every probability measure of the effective
  null.
* `ProbabilityTheory.isTestSupermartingale_iidNull_convexHull`,
  `ProbabilityTheory.isTestSupermartingale_infinitePi_of_tendsto` [EVR26, Note 32, Statement 1]:
  it is a test supermartingale for the i.i.d. null of the convex hull, and, on a countable
  alphabet, for the i.i.d. law of every pointwise limit of mixtures of members of the null.
* `ProbabilityTheory.measure_hittingAfter_lt_top_le_of_tendsto` [EVR26, Note 32, Statement 1]: its
  test of level `α` rejects with probability at most `α` under these laws.
* `ProbabilityTheory.toENNReal_log_inv_div_maxEPower_le_lintegral_hittingAfter`
  [EVR26, Note 32, Statement 1]: the test of a test supermartingale for the i.i.d. null of laws
  that charge every point makes at least `log (1/α) / a₁` observations in expectation.

## Implementation notes

The statements and proofs are adapted from `EValuesResearch/Results/ConvexPieces.lean` (commit
`83205cb`) in the paper project `RemyDegenne/evalues_research`, rewritten on the API of
LMLExplore: the closure of the null is reached through its effective null, and the bound on
expected stopping times is derived from the bound for every sequential test of the independent
null.

## References

* [EVR26] *Answers to open questions in e-values and anytime-valid inference*, notes 01 to 34 and
  the Lean library `EValuesResearch` of github.com/RemyDegenne/evalues_research, 2026; written and
  refereed by AI agents.
-/

public section

open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace ProbabilityTheory

variable {𝓧 : Type*} {m𝓧 : MeasurableSpace 𝓧} {S₁ : Set (Measure 𝓧)}
  {M : ℕ → (ℕ → 𝓧) → ℝ≥0∞}

/-! ### Test supermartingales of a null of laws that charge every point -/

variable [MeasurableSingletonClass 𝓧]

/-- The one-step condition of a test supermartingale of the i.i.d. null of laws that charge every
point, at every past, for every member of the effective null. -/
private lemma lintegral_update_le_of_mem_effectiveSet (hS₁ : ∀ P ∈ S₁, IsProbabilityMeasure P)
    (hpos : ∀ P ∈ S₁, ∀ x, P {x} ≠ 0) (hM : IsENNSupermartingale M Filtration.piLT (iidNull S₁))
    (n : ℕ) (ω : ℕ → 𝓧) {μ : Measure 𝓧} (hμ : μ ∈ effectiveSet S₁) :
    ∫⁻ y, M (n + 1) (Function.update ω n y) ∂μ ≤ M n ω := by
  refine lintegral_le_of_mem_effectiveSet hμ
    (((hM.adapted (n + 1)).mono (Filtration.le _ _) le_rfl).comp (measurable_update ω))
    fun P hP ↦ ?_
  have := hS₁ P hP
  exact (hM.anti_set (singleton_subset_iff.2
    (infinitePi_mem_iidNull hP))).lintegral_update_le_of_infinitePi fun i _ ↦ hpos P hP (ω i)

/-- **Test supermartingales see the effective null.** Let `S₁` be a set of probability measures
on `𝓧`, each of which charges every point. A test supermartingale for the i.i.d. null of `S₁`, in
the filtration `Filtration.piLT` of the past observations, is a test supermartingale for the
sequential null of the probability measures of the effective null of `S₁`: the laws under which
every observation, given the past, has a law under which every e-variable for `S₁` has mean at
most `1`. -/
theorem isTestSupermartingale_sequentialNull_effectiveSet_of_iidNull
    (hS₁ : ∀ P ∈ S₁, IsProbabilityMeasure P) (hpos : ∀ P ∈ S₁, ∀ x, P {x} ≠ 0)
    (hM : IsTestSupermartingale M Filtration.piLT (iidNull S₁)) :
    IsTestSupermartingale M Filtration.piLT (sequentialNull
      (fun _ _ ↦ effectiveSet S₁ ∩ {P | IsProbabilityMeasure P}) (fun k ω ↦ ω k)
      Filtration.piLT) := by
  refine ⟨isENNSupermartingale_sequentialNull_of_lintegral_update_le hM.adapted
    fun n ω ν hν ↦ lintegral_update_le_of_mem_effectiveSet hS₁ hpos hM.toIsENNSupermartingale n
      ω hν.1, fun P hP ↦ ?_⟩
  -- the initial value is a constant `c`, and `c ≤ 1` on the null, hence on its effective null
  have := isProbabilityMeasure_of_mem_sequentialNull hP
  obtain ⟨κ, -, hκS⟩ := exists_hasCondLaw_of_mem_sequentialNull hP 0
  obtain ⟨ω₀, hω₀, hω₀P⟩ := hκS.exists
  have : IsProbabilityMeasure (κ ω₀) := hω₀P
  have hconst : ∀ ω, M 0 ω = M 0 ω₀ := fun ω ↦ (hM.adapted 0).apply_eq_of_piLT_zero ω ω₀
  have h1 := lintegral_le_of_mem_effectiveSet hω₀ (measurable_const (a := M 0 ω₀))
    fun Q hQ ↦ by
      have := hS₁ Q hQ
      simpa [hconst] using hM.lintegral_zero_le _ (infinitePi_mem_iidNull hQ)
  simpa [hconst] using h1

/-- **The tests of a test supermartingale have level `α` on the effective null.** Let `S₁` be a
set of probability measures on `𝓧`, each of which charges every point, and `M` a test
supermartingale for the i.i.d. null of `S₁`, in the filtration `Filtration.piLT` of the past
observations. The test that rejects the first time `M` reaches `α⁻¹` has level `α` for the i.i.d.
law of every probability measure `Q₁` of the effective null of `S₁`. -/
theorem isLevelStoppingTime_hittingAfter_infinitePi_of_mem_effectiveSet
    (hS₁ : ∀ P ∈ S₁, IsProbabilityMeasure P) (hpos : ∀ P ∈ S₁, ∀ x, P {x} ≠ 0)
    (hM : IsTestSupermartingale M Filtration.piLT (iidNull S₁)) {Q₁ : Measure 𝓧}
    [IsProbabilityMeasure Q₁] (hQ₁ : Q₁ ∈ effectiveSet S₁) (α : ℝ≥0∞) :
    IsLevelStoppingTime (hittingAfter M (Ici α⁻¹) 0) Filtration.piLT
      {Measure.infinitePi fun _ : ℕ ↦ Q₁} α :=
  have hQ₁' : Q₁ ∈ effectiveSet S₁ ∩ {P | IsProbabilityMeasure P} := ⟨hQ₁, inferInstance⟩
  (((isTestSupermartingale_sequentialNull_effectiveSet_of_iidNull hS₁ hpos hM).anti_set
    (singleton_subset_iff.2 (infinitePi_mem_sequentialNull fun _ ↦ .of_forall fun _ ↦
      hQ₁'))).isEProcess (by rintro _ rfl; infer_instance)).isLevelStoppingTime_hittingAfter α

/-- **Test supermartingales see the convex hull of the null** [EVR26, Note 32, Statement 1].
Let `S₁` be a set of probability measures on `𝓧`, each of which charges every point. A test
supermartingale for the i.i.d. null of `S₁`, in the filtration `Filtration.piLT` of the past
observations, is a test supermartingale for the i.i.d. null of the convex hull of `S₁`. -/
theorem isTestSupermartingale_iidNull_convexHull (hS₁ : ∀ P ∈ S₁, IsProbabilityMeasure P)
    (hpos : ∀ P ∈ S₁, ∀ x, P {x} ≠ 0)
    (hM : IsTestSupermartingale M Filtration.piLT (iidNull S₁)) :
    IsTestSupermartingale M Filtration.piLT (iidNull (convexHull ℝ≥0∞ S₁)) :=
  (isTestSupermartingale_sequentialNull_effectiveSet_of_iidNull hS₁ hpos hM).anti_set
    ((iidNull_mono (subset_inter convexHull_subset_effectiveSet
      (convexHull_min (fun P hP ↦ hS₁ P hP) convex_setOfPred_isProbabilityMeasure))).trans
    (iidNull_subset_sequentialNull fun _ hP ↦ hP.2))

/-- **Test supermartingales see the closed convex hull of the null**
[EVR26, Note 32, Statement 1]. Let `S₁` be a set of probability measures on a countable alphabet
`𝓧`, each of which charges every point. A test supermartingale for the i.i.d. null of `S₁`, in the
filtration `Filtration.piLT` of the past observations, is a test supermartingale for the i.i.d.
law of every probability measure `Q₁` whose masses `Q₁ {x}` are the limits, along a filter, of
those of mixtures of members of `S₁`: for the closure of the convex hull of `S₁` in the topology of
pointwise convergence of the masses. -/
theorem isTestSupermartingale_infinitePi_of_tendsto [Countable 𝓧]
    (hS₁ : ∀ P ∈ S₁, IsProbabilityMeasure P) (hpos : ∀ P ∈ S₁, ∀ x, P {x} ≠ 0)
    (hM : IsTestSupermartingale M Filtration.piLT (iidNull S₁))
    {ι : Type*} {l : Filter ι} [l.NeBot] {R : ι → Measure 𝓧}
    (hR : ∀ᶠ i in l, R i ∈ convexHull ℝ≥0∞ S₁) (Q₁ : Measure 𝓧) [IsProbabilityMeasure Q₁]
    (hQ₁ : ∀ x, Tendsto (fun i ↦ R i {x}) l (𝓝 (Q₁ {x}))) :
    IsTestSupermartingale M Filtration.piLT {Measure.infinitePi fun _ : ℕ ↦ Q₁} := by
  -- `Q₁` is in the effective null, by Fatou's lemma for sums
  have hQ : Q₁ ∈ effectiveSet S₁ := by
    refine mem_effectiveSet_of_measure_le_liminf (hR.mono fun i hi ↦
      convexHull_subset_effectiveSet hi) fun s hs ↦ ?_
    simpa [lintegral_indicator_one hs] using
      lintegral_le_liminf_of_tendsto_measure_singleton hQ₁ (s.indicator 1)
  exact (isTestSupermartingale_sequentialNull_effectiveSet_of_iidNull hS₁ hpos hM).anti_set
    (singleton_subset_iff.2 (infinitePi_mem_sequentialNull fun _ ↦ .of_forall fun _ ↦
      (show Q₁ ∈ effectiveSet S₁ ∩ {P | IsProbabilityMeasure P} from ⟨hQ, inferInstance⟩)))

/-- **The tests of the test supermartingales of a null have no power inside its closed convex
hull** [EVR26, Note 32, Statement 1]. Under the hypotheses of
`isTestSupermartingale_infinitePi_of_tendsto`, the test that rejects the first time `M` reaches
`α⁻¹` rejects with probability at most `α` under the i.i.d. law of every probability measure
`Q₁` whose masses are limits of those of mixtures of members of the null. -/
theorem measure_hittingAfter_lt_top_le_of_tendsto [Countable 𝓧]
    (hS₁ : ∀ P ∈ S₁, IsProbabilityMeasure P) (hpos : ∀ P ∈ S₁, ∀ x, P {x} ≠ 0)
    (hM : IsTestSupermartingale M Filtration.piLT (iidNull S₁))
    {ι : Type*} {l : Filter ι} [l.NeBot] {R : ι → Measure 𝓧}
    (hR : ∀ᶠ i in l, R i ∈ convexHull ℝ≥0∞ S₁) (Q₁ : Measure 𝓧) [IsProbabilityMeasure Q₁]
    (hQ₁ : ∀ x, Tendsto (fun i ↦ R i {x}) l (𝓝 (Q₁ {x}))) (α : ℝ≥0∞) :
    Measure.infinitePi (fun _ : ℕ ↦ Q₁) {ω | hittingAfter M (Ici α⁻¹) 0 ω < ⊤} ≤ α :=
  ((isTestSupermartingale_infinitePi_of_tendsto hS₁ hpos hM hR Q₁ hQ₁).isEProcess
    (by rintro _ rfl; infer_instance)).isLevelStoppingTime_hittingAfter α |>.measure_lt_top_le _ rfl

/-- **The tests of the test supermartingales of a null make at least `log (1/α) / a₁`
observations** [EVR26, Note 32, Statement 1]. Let `S₁` be a set of probability measures on `𝓧`,
each of which charges every point, `M` a test supermartingale for the i.i.d. null of `S₁` in the
filtration `Filtration.piLT` of the past observations, and `Q₁` a probability measure. The test
that rejects the first time `M` reaches `α⁻¹` makes at least `log (1/α) / a₁` observations in
expectation under the i.i.d. law of `Q₁`, where `a₁ = maxEPower Q₁ S₁` is the largest expected
logarithm of an e-variable of one observation (`maxLogGrowth Q₁ S₁ 1`, by
`ProbabilityTheory.maxLogGrowth_one`). The left side is in `ℝ≥0∞`, with `log (1/α)` replaced by
`0` for `α ≥ 1`. -/
theorem toENNReal_log_inv_div_maxEPower_le_lintegral_hittingAfter
    (hS₁ : ∀ P ∈ S₁, IsProbabilityMeasure P) (hpos : ∀ P ∈ S₁, ∀ x, P {x} ≠ 0)
    (hM : IsTestSupermartingale M Filtration.piLT (iidNull S₁))
    (Q₁ : Measure 𝓧) [IsProbabilityMeasure Q₁] (α : ℝ≥0∞) :
    (ENNReal.log α⁻¹).toENNReal / (maxEPower Q₁ S₁).toENNReal ≤
      ∫⁻ ω, ENat.toENNReal (hittingAfter M (Ici α⁻¹) 0 ω)
        ∂Measure.infinitePi (fun _ : ℕ ↦ Q₁) := by
  -- `M` is a test supermartingale for the independent null, hence an e-process
  have hM' : IsTestSupermartingale M Filtration.piLT (indepNull S₁) :=
    (isTestSupermartingale_sequentialNull_effectiveSet_of_iidNull hS₁ hpos hM).anti_set
      ((indepNull_mono (subset_inter subset_effectiveSet fun P hP ↦ hS₁ P hP)).trans
        (indepNull_subset_sequentialNull fun _ hP ↦ hP.2))
  exact toENNReal_log_inv_div_maxEPower_le_lintegral_of_indepNull Q₁ hS₁
    ((hM'.isEProcess fun P hP ↦ have := isProbabilityMeasure_of_mem_indepNull hS₁ P hP;
      inferInstance).isLevelStoppingTime_hittingAfter α)

end ProbabilityTheory
