/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.EValues.EProcess.StoppedNull
public import LMLExplore.EValues.EffectiveSet.CountableMixture
public import LMLExplore.EValues.KLInf

/-!
# Optimal e-processes

E-processes for a null `S` are the e-variables of the stopped null `stoppedNull ℱ S` on the space
of stopped paths (`isEProcess_iff_isEVar_stoppedNull`). Statlib's existence of numeraires then
gives, for every null of measures of mass at most one and every finite measure on the stopped
paths, an e-process that is a numeraire, with no dominating measure. For the mixture over a
probability measure `ρ` on the times of the stopped laws of a probability measure `Q` at the
constant times, this is an e-process `E*` with `∑' n, ρ {n} * ∫⁻ E n / E* n ∂Q ≤ 1` for every
e-process `E` [EVR26, Note 40, Theorem 1], the form without a dominating measure of
[KG22, Theorem 5]; it maximizes the expected logarithm over the e-processes, and the maximum is the
smallest relative entropy from the mixture to the effective null of the stopped null, by the
duality of [LRR25].

The identity of [KG22, Theorem 5] puts the mixtures of the stopped laws of the null on the dual
side. For a null dominated by an s-finite measure, the stopped null is dominated by a finite
measure on the stopped paths, and the countable mixtures of its members suffice: the largest
e-power is the infimum of the relative entropy to the countable mixtures of stopped laws, by the
bipolar theorem in the form of [EVR26, Note 48, Theorem 2]. Without domination the identity fails,
already with countable mixtures [EVR26, Note 40, Example 4]: for the null of all Dirac masses on
`ℕ → 𝓧` every e-process is at most one, so the largest e-power vanishes, while a countable mixture
of stopped laws of Dirac masses sees, at a time `n ≠ 0`, only countably many first observations,
and has infinite relative entropy from the stopped law of an alternative whose first observation
has no atom.

## Main statements

* `ProbabilityTheory.exists_isEProcess_isNumeraire_stoppedNull`: for every finite measure on the
  stopped paths, some e-process is a numeraire of the stopped null.
* `ProbabilityTheory.isGreatest_eintegral_log_isEProcess`: under a probability measure on the
  stopped paths, the largest expected logarithm of an e-process is the smallest relative entropy
  to the effective null of the stopped null, and it is attained.
* `ProbabilityTheory.exists_isEProcess_forall_tsum_lintegral_div_le_one`: for probability
  measures `Q` on `Ω` and `ρ` on the times, some e-process `E*` has
  `∑' n, ρ {n} * ∫⁻ E n / E* n ∂Q ≤ 1` for every e-process `E` [EVR26, Note 40, Theorem 1].
* `ProbabilityTheory.maxEPower_stoppedNull_eq_iInf_klIntegral_sigmaConvexHull`,
  `ProbabilityTheory.isGreatest_eintegral_log_isEProcess_sigmaConvexHull`: **the identity of
  Koolen and Grünwald for a dominated null**, with the countable mixtures of stopped laws on the
  dual side [KG22, Theorem 5].
* `ProbabilityTheory.isEVar_stoppedNull_range_dirac_iff`,
  `ProbabilityTheory.isEProcess_range_dirac_iff`,
  `ProbabilityTheory.maxEPower_stoppedNull_range_dirac`: the e-variables of the stopped null and
  the e-processes of the null of all Dirac masses are the functions at most one, and the largest
  e-power vanishes.
* `ProbabilityTheory.iInf_klIntegral_sigmaConvexHull_stoppedNull_range_dirac`,
  `ProbabilityTheory.maxEPower_stoppedNull_range_dirac_lt_iInf_klIntegral_sigmaConvexHull`,
  `maxEPower_stoppedNull_range_dirac_lt_iInf_klIntegral_sigmaConvexHull_infinitePi`:
  **the identity fails without domination**, with countable mixtures and hence with finite ones
  [EVR26, Note 40, Example 4].

## Implementation notes

The existence of optimal e-processes is adapted from the file `notes/lean-wip/StoppedPaths.lean`
(commit `c6c6ba8`) of the paper project `RemyDegenne/evalues_research` (Apache 2.0), with the
stopped paths carrying Tau Ceti's progressive σ-algebra in place of a σ-algebra of its own.

## References

* [KG22] W. M. Koolen and P. Grünwald, *Log-optimal anytime-valid e-values*, Int. J. Approx.
  Reason. 141 (2022), Theorem 5.
* [EVR26] *Answers to open questions in e-values and anytime-valid inference*, the notes and the
  Lean library `EValuesResearch` of github.com/RemyDegenne/evalues_research, 2026, Notes 40
  and 48.
* [LRR25] M. Larsson, A. Ramdas and J. Ruf, *The numeraire e-variable and reverse information
  projection*, Ann. Statist. 53 (2025), arXiv:2402.18810v4.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℕ mΩ} {S : Set (Measure Ω)}

/-- **Existence of an optimal e-process.** For a null of measures of mass at most one, with no
dominating measure, and every finite measure `R` on the stopped paths, some e-process `E` for `S`
is a numeraire of the stopped null against `R`: `Function.uncurry E` maximizes the expected
logarithm under `R`, and `∫⁻ Function.uncurry F / Function.uncurry E ∂R ≤ 1` for every
e-process `F` when `R` is a probability measure. -/
theorem exists_isEProcess_isNumeraire_stoppedNull (hS : ∀ P ∈ S, P univ ≤ 1)
    (R : @Measure (ℕ × Ω) ℱ.progressive) [IsFiniteMeasure R] :
    ∃ E : ℕ → Ω → ℝ≥0∞, IsEProcess E ℱ S ∧
      IsNumeraire (Function.uncurry E) (stoppedNull ℱ S) R := by
  obtain ⟨X, hX⟩ := exists_isNumeraire R (stoppedNull ℱ S) fun _ ↦
    measure_univ_le_one_of_mem_stoppedNull hS
  rw [← Function.uncurry_curry X] at hX
  exact ⟨Function.curry X, isEProcess_iff_isEVar_stoppedNull.2 hX.isEVar, hX⟩

/-- **The largest expected logarithm of an e-process.** For a null of measures of mass at most
one and a probability measure `R` on the stopped paths, the expected logarithms under `R` of the
e-processes, read on the stopped paths, have a largest element, the smallest relative entropy
from `R` to the effective null of the stopped null. -/
theorem isGreatest_eintegral_log_isEProcess (hS : ∀ P ∈ S, P univ ≤ 1)
    (R : @Measure (ℕ × Ω) ℱ.progressive) [IsProbabilityMeasure R] :
    IsGreatest ((fun F : ℕ → Ω → ℝ≥0∞ ↦ ∫ᵉ x, ENNReal.log (Function.uncurry F x) ∂R) ''
      {F | IsEProcess F ℱ S}) (klInf R (effectiveSet (stoppedNull ℱ S))) := by
  have hS' : ∀ μ ∈ stoppedNull ℱ S, μ univ ≤ 1 := fun _ ↦ measure_univ_le_one_of_mem_stoppedNull hS
  rw [← maxEPower_eq_klInf_effectiveSet hS']
  obtain ⟨E, hE, hX⟩ := exists_isEProcess_isNumeraire_stoppedNull hS R
  refine ⟨⟨E, hE, ?_⟩, ?_⟩
  · rw [maxEPower_def, hX.maxUtility_eq_eintegral]
  · rintro _ ⟨F, hF, rfl⟩
    exact (isEProcess_iff_isEVar_stoppedNull.1 hF).eintegral_log_le_maxEPower R

/-- **An e-process that is optimal for a distribution over times** [EVR26, Note 40, Theorem 1;
KG22, Theorem 5]. For a null
of measures of mass at most one, with no dominating measure, and probability measures `Q` on `Ω`
and `ρ` on the times, some e-process `E*` satisfies `∑' n, ρ {n} * ∫⁻ E n / E* n ∂Q ≤ 1` for
every e-process `E`. It is the numeraire of the stopped null against the mixture
`Measure.sum fun n ↦ ρ {n} • stoppedLaw ℱ Q fun _ ↦ n` of the stopped laws of `Q` at the constant
times, so that `isGreatest_eintegral_log_isEProcess` computes its expected logarithm under the
mixture. -/
theorem exists_isEProcess_forall_tsum_lintegral_div_le_one (hS : ∀ P ∈ S, P univ ≤ 1)
    (Q : Measure Ω) [IsProbabilityMeasure Q] (ρ : Measure ℕ) [IsProbabilityMeasure ρ] :
    ∃ E : ℕ → Ω → ℝ≥0∞, IsEProcess E ℱ S ∧
      IsNumeraire (Function.uncurry E) (stoppedNull ℱ S)
        (Measure.sum fun n ↦ ρ {n} • stoppedLaw ℱ Q fun _ ↦ n) ∧
      ∀ F : ℕ → Ω → ℝ≥0∞, IsEProcess F ℱ S → ∑' n, ρ {n} * ∫⁻ ω, F n ω / E n ω ∂Q ≤ 1 := by
  obtain ⟨E, hE, hX⟩ := exists_isEProcess_isNumeraire_stoppedNull hS
    (Measure.sum fun n ↦ ρ {n} • stoppedLaw ℱ Q fun _ ↦ n)
  refine ⟨E, hE, hX, fun F hF ↦ ?_⟩
  have hF' := isEProcess_iff_isEVar_stoppedNull.1 hF
  have h := hX.lintegral_div_le_one hF'
  rwa [lintegral_sum_smul_stoppedLaw_const ρ Q
    (f := fun x ↦ Function.uncurry F x / Function.uncurry E x)
    (hF'.measurable.div hX.measurable)] at h

/-! ### Countable mixtures of stopped laws for a dominated null -/

/-- **The identity of Koolen and Grünwald for a dominated null** [KG22, Theorem 5; EVR26, Note 40].
For a null `S` of measures of mass at most one, absolutely continuous with respect to an s-finite
measure `μ`, and every probability measure `R` on the stopped paths, the largest e-power of the
stopped null under `R` is the infimum of the relative entropy `klIntegral R m` over the countable
mixtures `m` of stopped laws of members of `S`. For `R` the mixture
`Measure.sum fun n ↦ ρ {n} • stoppedLaw ℱ Q fun _ ↦ n` over a probability measure `ρ` on the times,
the left side is the expected logarithm of the optimal e-process of
`exists_isEProcess_forall_tsum_lintegral_div_le_one`. -/
theorem maxEPower_stoppedNull_eq_iInf_klIntegral_sigmaConvexHull {μ : Measure Ω} [SFinite μ]
    (hSμ : ∀ P ∈ S, P ≪ μ) (hS : ∀ P ∈ S, P univ ≤ 1)
    (R : @Measure (ℕ × Ω) ℱ.progressive) [IsProbabilityMeasure R] :
    maxEPower R (stoppedNull ℱ S) = ⨅ m ∈ sigmaConvexHull (stoppedNull ℱ S), klIntegral R m := by
  obtain ⟨ν, hν, hSν⟩ := exists_isFiniteMeasure_forall_stoppedLaw_absolutelyContinuous (ℱ := ℱ) μ
  refine maxEPower_eq_iInf_klIntegral_sigmaConvexHull (μ := ν) ?_
    fun _ ↦ measure_univ_le_one_of_mem_stoppedNull hS
  intro m hm
  obtain ⟨P, hP, τ, hτ, -, rfl⟩ := mem_stoppedNull.1 hm
  exact hSν (hSμ P hP) hτ.measurable'.untopA

/-- **The largest expected logarithm of an e-process, for a dominated null** [KG22, Theorem 5].
For a null `S` of measures of mass at most one, absolutely continuous with respect to an s-finite
measure, and a probability measure `R` on the stopped paths, the largest expected logarithm under
`R` of an e-process, read on the stopped paths, is the infimum of `klIntegral R m` over the
countable mixtures `m` of stopped laws of members of `S`. -/
theorem isGreatest_eintegral_log_isEProcess_sigmaConvexHull {μ : Measure Ω} [SFinite μ]
    (hSμ : ∀ P ∈ S, P ≪ μ) (hS : ∀ P ∈ S, P univ ≤ 1)
    (R : @Measure (ℕ × Ω) ℱ.progressive) [IsProbabilityMeasure R] :
    IsGreatest ((fun F : ℕ → Ω → ℝ≥0∞ ↦ ∫ᵉ x, ENNReal.log (Function.uncurry F x) ∂R) ''
      {F | IsEProcess F ℱ S}) (⨅ m ∈ sigmaConvexHull (stoppedNull ℱ S), klIntegral R m) := by
  rw [← maxEPower_stoppedNull_eq_iInf_klIntegral_sigmaConvexHull hSμ hS R,
    maxEPower_eq_klInf_effectiveSet fun _ ↦ measure_univ_le_one_of_mem_stoppedNull hS]
  exact isGreatest_eintegral_log_isEProcess hS R

/-! ### The null of all Dirac masses -/

/-- **The e-variables of the stopped null of the Dirac masses** are the progressive functions of
the stopped paths that are at most one everywhere: the stopped law of the Dirac mass at `ω` at the
constant time `n` evaluates a function at `(n, ω)`. -/
theorem isEVar_stoppedNull_range_dirac_iff {X : ℕ × Ω → ℝ≥0∞} :
    IsEVar X (stoppedNull ℱ (range Measure.dirac)) ↔
      Measurable[ℱ.progressive] X ∧ ∀ x, X x ≤ 1 := by
  refine ⟨fun hX ↦ ⟨hX.measurable, fun ⟨n, ω⟩ ↦ ?_⟩, fun ⟨hX, hX1⟩ ↦ ⟨hX, fun μ hμ ↦ ?_⟩⟩
  · have h := hX.lintegral_le_one (stoppedLaw_mem_stoppedNull (mem_range_self ω)
      (isStoppingTime_natCast (ℱ := ℱ) n) fun _ ↦ WithTop.natCast_ne_top n)
    simp only [WithTop.untopA_natCast] at h
    rwa [lintegral_stoppedLaw measurable_const hX.measurable, lintegral_dirac' ω
      (f := fun ω' ↦ X (n, ω'))
      (hX.measurable.comp (Filtration.measurable_prodMk_progressive measurable_const))] at h
  · calc ∫⁻ x, X x ∂μ ≤ ∫⁻ _, 1 ∂μ := lintegral_mono hX1
      _ = μ univ := lintegral_one
      _ ≤ 1 := measure_univ_le_one_of_mem_stoppedNull
        (forall_mem_range.2 fun _ ↦ prob_le_one) hμ

/-- **The e-processes of the null of all Dirac masses** are the adapted processes that are at most
one everywhere. -/
theorem isEProcess_range_dirac_iff {E : ℕ → Ω → ℝ≥0∞} :
    IsEProcess E ℱ (range Measure.dirac) ↔ Adapted ℱ E ∧ ∀ n ω, E n ω ≤ 1 := by
  rw [isEProcess_iff_isEVar_stoppedNull, isEVar_stoppedNull_range_dirac_iff,
    Filtration.measurable_uncurry_progressive_iff, Prod.forall]
  simp only [Function.uncurry_apply_pair]

/-- The largest e-power of the stopped null of the Dirac masses vanishes under every measure on the
stopped paths: its e-variables are at most one, and the constant `1` is one of them. -/
theorem maxEPower_stoppedNull_range_dirac (R : @Measure (ℕ × Ω) ℱ.progressive) :
    maxEPower R (stoppedNull ℱ (range Measure.dirac)) = 0 := by
  refine le_antisymm (maxEPower_le_iff.2 fun X hX ↦ eintegral_nonpos fun x ↦ ?_)
    (maxEPower_nonneg R fun _ ↦ measure_univ_le_one_of_mem_stoppedNull
      (forall_mem_range.2 fun _ ↦ prob_le_one))
  exact ENNReal.log_le_zero_iff.2 ((isEVar_stoppedNull_range_dirac_iff.1 hX).2 x)

/-! ### Countable mixtures do not suffice without domination -/

section Canonical

variable {𝓧 : Type*} [MeasurableSpace 𝓧] [MeasurableSingletonClass 𝓧] {Q : Measure (ℕ → 𝓧)}
  {n : ℕ}

/-- On the canonical space `ℕ → 𝓧` with the filtration `Filtration.piLT` of the past observations,
let `Q` be a nonzero measure under which the first observation has no atom. At a time `n ≠ 0`, the
stopped law of `Q` at the constant time `n` is not absolutely continuous with respect to any
countable mixture of stopped laws of Dirac masses: such a mixture is carried, at time `n`, by the
paths whose first observation is in a countable set, which `Q` does not charge. -/
theorem not_stoppedLaw_absolutelyContinuous_of_mem_sigmaConvexHull [NeZero Q]
    (hQ : ∀ x, Q {ω | ω 0 = x} = 0) (hn : n ≠ 0)
    {m : @Measure (ℕ × (ℕ → 𝓧)) (Filtration.piLT (X := fun _ ↦ 𝓧)).progressive}
    (hm : m ∈ sigmaConvexHull
      (stoppedNull (Filtration.piLT (X := fun _ ↦ 𝓧)) (range Measure.dirac))) :
    ¬ stoppedLaw (Filtration.piLT (X := fun _ ↦ 𝓧)) Q (fun _ ↦ n) ≪ m := by
  obtain ⟨w, Qs, -, hQs, rfl⟩ := mem_sigmaConvexHull_iff.1 hm
  choose P hP τ hτ _ hQs_eq using fun k ↦ mem_stoppedNull.1 (hQs k)
  choose ω hω using hP
  -- the set `A` of the stopped paths at time `n` whose first observation is not one of those of
  -- the paths `ω k` that carry the mixture
  have hC : MeasurableSet (range fun k ↦ ω k 0) := (countable_range _).measurableSet
  set A : Set (ℕ × (ℕ → 𝓧)) := {x | x.1 = n ∧ x.2 0 ∉ range fun k ↦ ω k 0} with hA_def
  have hA : MeasurableSet[(Filtration.piLT (X := fun _ ↦ 𝓧)).progressive] A := by
    refine Filtration.measurableSet_progressive_iff_of_countable.2 fun i ↦ ?_
    rcases eq_or_ne i n with rfl | hi
    · convert Filtration.measurable_piLT_apply (X := fun _ ↦ 𝓧) (Nat.pos_of_ne_zero hn)
        hC.compl using 1
      ext
      simp [hA_def]
    · simp [hA_def, hi]
  have hmA : (Measure.sum fun k ↦ w k • Qs k) A = 0 := by
    rw [Measure.sum_apply _ hA]
    refine tsum_eq_zero_iff.2 fun k ↦ ?_
    have hs : MeasurableSet {ω' | ((τ k ω').untopA, ω') ∈ A} :=
      Filtration.measurable_prodMk_progressive (hτ k).measurable'.untopA hA
    rw [smul_apply, ← hQs_eq k, stoppedLaw_apply (hτ k).measurable'.untopA hA, ← hω k,
      Measure.dirac_apply' _ hs, indicator_of_notMem (by simp [hA_def]), smul_zero]
  refine fun hac ↦ NeZero.ne Q (Measure.measure_univ_eq_zero.1 ?_)
  have hQA := hac hmA
  rw [stoppedLaw_apply measurable_const hA] at hQA
  have hQC : Q {ω' | ω' 0 ∈ range fun k ↦ ω k 0} = 0 :=
    measure_mono_null (fun ω' ⟨k, hk⟩ ↦ mem_iUnion.2 ⟨k, hk.symm⟩)
      (measure_iUnion_null fun k ↦ hQ (ω k 0))
  refine measure_mono_null (fun ω' _ ↦ ?_) (measure_union_null hQA hQC)
  by_cases h : ω' 0 ∈ range fun k ↦ ω k 0
  · exact Or.inr h
  · exact Or.inl (by simpa [hA_def] using h)

/-- **Countable mixtures of stopped laws do not suffice without domination** [EVR26, Note 40,
Example 4]. On the canonical space `ℕ → 𝓧` with the filtration `Filtration.piLT`, let `Q` be a
nonzero measure under which the first observation has no atom. At a time `n ≠ 0`, every countable
mixture of stopped laws of Dirac masses has infinite relative entropy from the stopped law of `Q`
at the constant time `n`. Finite mixtures are countable mixtures
(`MeasureTheory.convexHull_subset_sigmaConvexHull`). -/
theorem iInf_klIntegral_sigmaConvexHull_stoppedNull_range_dirac [NeZero Q]
    (hQ : ∀ x, Q {ω | ω 0 = x} = 0) (hn : n ≠ 0) :
    ⨅ m ∈ sigmaConvexHull (stoppedNull (Filtration.piLT (X := fun _ ↦ 𝓧)) (range Measure.dirac)),
      klIntegral (stoppedLaw (Filtration.piLT (X := fun _ ↦ 𝓧)) Q fun _ ↦ n) m = ⊤ :=
  iInf₂_eq_top.2 fun _ hm ↦
    klIntegral_of_not_ac (not_stoppedLaw_absolutelyContinuous_of_mem_sigmaConvexHull hQ hn hm)

/-- **The identity of Koolen and Grünwald fails with countable mixtures without domination**
[EVR26, Note 40, Example 4]. For the null of all Dirac masses on the canonical space `ℕ → 𝓧`, with
the filtration `Filtration.piLT`, and a nonzero measure `Q` under which the first observation has
no atom, the largest e-power of the stopped null under the stopped law of `Q` at a constant time
`n ≠ 0` is `0`, while the infimum of the relative entropy from that law to the countable mixtures
of stopped laws of the null is `∞`. -/
theorem maxEPower_stoppedNull_range_dirac_lt_iInf_klIntegral_sigmaConvexHull [NeZero Q]
    (hQ : ∀ x, Q {ω | ω 0 = x} = 0) (hn : n ≠ 0) :
    maxEPower (stoppedLaw (Filtration.piLT (X := fun _ ↦ 𝓧)) Q fun _ ↦ n)
        (stoppedNull (Filtration.piLT (X := fun _ ↦ 𝓧)) (range Measure.dirac)) <
      ⨅ m ∈ sigmaConvexHull (stoppedNull (Filtration.piLT (X := fun _ ↦ 𝓧)) (range Measure.dirac)),
        klIntegral (stoppedLaw (Filtration.piLT (X := fun _ ↦ 𝓧)) Q fun _ ↦ n) m := by
  rw [maxEPower_stoppedNull_range_dirac,
    iInf_klIntegral_sigmaConvexHull_stoppedNull_range_dirac hQ hn]
  exact EReal.zero_lt_top

/-- **Countable mixtures of stopped laws do not suffice for i.i.d. alternatives**
[EVR26, Note 40, Example 4]. For the null of all Dirac masses on `ℕ → 𝓧`, with the filtration
`Filtration.piLT`, and the i.i.d. law of a marginal `Q₁` without atoms, such as the product of
Lebesgue measures on `[0, 1]`, the largest e-power of the stopped null at a constant time `n ≠ 0`
is below the infimum of the relative entropy to the countable mixtures of stopped laws of the
null. -/
theorem maxEPower_stoppedNull_range_dirac_lt_iInf_klIntegral_sigmaConvexHull_infinitePi
    (Q₁ : Measure 𝓧) [IsProbabilityMeasure Q₁] [NullSingletonClass Q₁] (hn : n ≠ 0) :
    maxEPower (stoppedLaw (Filtration.piLT (X := fun _ ↦ 𝓧))
        (Measure.infinitePi fun _ ↦ Q₁) fun _ ↦ n)
        (stoppedNull (Filtration.piLT (X := fun _ ↦ 𝓧)) (range Measure.dirac)) <
      ⨅ m ∈ sigmaConvexHull (stoppedNull (Filtration.piLT (X := fun _ ↦ 𝓧)) (range Measure.dirac)),
        klIntegral (stoppedLaw (Filtration.piLT (X := fun _ ↦ 𝓧))
          (Measure.infinitePi fun _ ↦ Q₁) fun _ ↦ n) m :=
  maxEPower_stoppedNull_range_dirac_lt_iInf_klIntegral_sigmaConvexHull (fun x ↦ by
    simpa [Set.preimage] using
      (measurePreserving_eval_infinitePi (fun _ : ℕ ↦ Q₁) 0).measure_preimage
        (measurableSet_singleton x).nullMeasurableSet) hn

end Canonical

end ProbabilityTheory
