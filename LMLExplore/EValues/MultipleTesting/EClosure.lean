/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.MeasureTheory.Integral.Lebesgue.Selection
public import Statlib.EValues.EVariable

/-!
# The e-Closure Principle

Hypotheses are indexed by a finite type `ι`, with nulls `H : ι → Set (Measure Ω)`; under a
probability measure `P` the true nulls are the indices `i` with `P ∈ H i` (`trueNulls H P`). A
loss `f N R : ℝ≥0∞` measures the error of rejecting the set `R` when the set of true nulls is `N`:
the false discovery proportion `fdp`, the indicator `fwerLoss` that some true null is rejected, the
number of false discoveries, or any other function, bounded or not. A candidate family
`𝓡 : Ω → Set (Finset ι)` controls the loss simultaneously at level `α` when
`∫⁻ ω, ⨆ R ∈ 𝓡 ω, f (trueNulls H P) R ∂P ≤ α` for every probability measure `P`: any rejection
set may be selected from `𝓡 ω` after seeing the data.

An e-collection (`ProbabilityTheory.IsECollection`) is a family `e S` of statistics, indexed by
the sets of hypotheses, with `e ∅ = 0`, such that `e (trueNulls H P)` has expectation at most one
under every probability measure `P` [XSF+26, Definition 5]; statistics `e S` that are e-variables
for the intersections `⋂ i ∈ S, H i` are one. Its e-closure at level `α` is the candidate family
of the sets `R` with `f S R ≤ α * e S ω` for every `S` (`ProbabilityTheory.eClosure`). The
e-Closure Principle [XSF+26, Theorem 6] states that a candidate family controls `f`
simultaneously at level `α` exactly when it is contained in the e-closure of some e-collection:
the e-closures form a complete class of multiple testing procedures, for every loss, under
arbitrary dependence and with no dominating measure.

The principle is proved in its post-hoc form [XSF+26, Theorem 48]: an e-collection controls, at
once, every loss of a family and every level, chosen after seeing the data, in the sense that
`∫⁻ ω, ⨆ k, ⨆ R ∈ eClosure (f k) (α k) e ω, f k (trueNulls H P) R / α k ∂P ≤ 1`; and conversely
every countable family of candidate families with this guarantee is contained in the e-closures
of one e-collection. The single loss and level of the e-Closure Principle, the single rejection
sets [XSF+26, Corollary 7], the family-wise error rate [XSF+26, Theorem 12] with the classical
closure principle [XSF+26, Corollary 13], and the false discovery rate [XSF+26, Theorem 14] are
its cases. Simultaneous control is control at every measurable data-dependent choice of a
rejection set [XSF+26, Lemma 4], through a measurable selection of a maximizer.

## Main definitions

* `ProbabilityTheory.trueNulls H P`: the true nulls under `P`.
* `ProbabilityTheory.fdp N R`: the false discovery proportion `#(R ∩ N) / max #R 1`.
* `ProbabilityTheory.fwerLoss N R`: the loss of the family-wise error, `1` when `R` meets `N`.
* `ProbabilityTheory.IsECollection e H`: `e` is an e-collection for the hypotheses `H`.
* `ProbabilityTheory.eClosure f α e ω`: the e-closure of `e` for the loss `f` at level `α`.
* `ProbabilityTheory.closedTesting A ω`: the closed testing rejection set of the rejection events
  `A S` of the intersection hypotheses.

## Main statements

* `ProbabilityTheory.IsECollection.lintegral_iSup_div_le_one`,
  `ProbabilityTheory.exists_isECollection_of_lintegral_iSup_div_le_one`: the post-hoc
  e-Closure Principle [XSF+26, Theorem 48].
* `ProbabilityTheory.forall_lintegral_iSup_le_iff_exists_isECollection`: the e-Closure
  Principle [XSF+26, Theorem 6].
* `ProbabilityTheory.forall_lintegral_le_iff_exists_isECollection`: its form for a single
  rejection set [XSF+26, Corollary 7].
* `ProbabilityTheory.forall_lintegral_iSup_le_iff_forall_lintegral_le`: simultaneous control is
  control at every measurable data-dependent choice [XSF+26, Lemma 4].
* `ProbabilityTheory.forall_measure_exists_not_disjoint_le_iff_exists_isECollection`: the
  e-Closure Principle for the family-wise error rate, with e-collections valued in `{0, α⁻¹}`
  [XSF+26, Theorem 12].
* `ProbabilityTheory.mem_eClosure_fwerLoss_indicator_iff`: the closed testing rejection set is the
  largest member of an e-closure for the family-wise loss [XSF+26, Corollary 13].
* `ProbabilityTheory.measure_not_disjoint_closedTesting_le`: the classical closure principle
  [XSF+26, Corollary 13].
* `ProbabilityTheory.forall_lintegral_iSup_fdp_le_iff_exists_isECollection`: the e-Closure
  Principle for the false discovery rate [XSF+26, Theorem 14].

## References

* [XSF+26] Z. Xu, A. Solari, L. Fischer, R. de Heide, A. Ramdas and J. Goeman, *Bringing closure
  to false discovery rate control: a general principle for multiple testing*,
  arXiv:2509.02517v3.
* [MPG76] R. Marcus, E. Peritz and K. R. Gabriel, *On closed testing procedures with special
  reference to ordered analysis of variance*, Biometrika 63 (1976).
-/

public section

open MeasureTheory Finset
open scoped ENNReal

namespace ProbabilityTheory

variable {Ω ι κ : Type*} {mΩ : MeasurableSpace Ω}

/-! ### Losses -/

section Losses

variable [DecidableEq ι] {N R : Finset ι}

/-- The false discovery proportion `#(R ∩ N) / max #R 1` of the rejection set `R` when the set of
true nulls is `N`. -/
noncomputable def fdp (N R : Finset ι) : ℝ≥0∞ :=
  #(R ∩ N) / max (#R : ℝ≥0∞) 1

theorem fdp_def (N R : Finset ι) : fdp N R = #(R ∩ N) / max (#R : ℝ≥0∞) 1 := (rfl)

@[simp]
theorem fdp_empty_left (R : Finset ι) : fdp ∅ R = 0 := by
  simp [fdp_def]

@[simp]
theorem fdp_empty_right (N : Finset ι) : fdp N ∅ = 0 := by
  simp [fdp_def]

/-- The false discovery proportion is at most one. -/
theorem fdp_le_one (N R : Finset ι) : fdp N R ≤ 1 := by
  rw [fdp_def]
  refine ENNReal.div_le_of_le_mul ?_
  rw [one_mul]
  exact (Nat.cast_le.2 (card_le_card inter_subset_left)).trans (le_max_left _ _)

/-- The loss of the family-wise error: `1` when the rejection set `R` contains a true null of `N`,
and `0` otherwise. -/
noncomputable def fwerLoss (N R : Finset ι) : ℝ≥0∞ :=
  if Disjoint R N then 0 else 1

theorem fwerLoss_def (N R : Finset ι) : fwerLoss N R = if Disjoint R N then 0 else 1 := (rfl)

@[simp]
theorem fwerLoss_of_disjoint (h : Disjoint R N) : fwerLoss N R = 0 := by
  simp [fwerLoss_def, h]

@[simp]
theorem fwerLoss_of_not_disjoint (h : ¬Disjoint R N) : fwerLoss N R = 1 := by
  simp [fwerLoss_def, h]

theorem fwerLoss_empty_left (R : Finset ι) : fwerLoss ∅ R = 0 :=
  fwerLoss_of_disjoint (disjoint_empty_right R)

theorem fwerLoss_empty_right (N : Finset ι) : fwerLoss N ∅ = 0 :=
  fwerLoss_of_disjoint (disjoint_empty_left N)

/-- The expected largest family-wise loss of a measurable candidate family is the probability
that some candidate contains a true null of `N`. -/
theorem lintegral_iSup_fwerLoss [Countable ι] {𝓡 : Ω → Set (Finset ι)} (h𝓡 : Measurable 𝓡)
    (N : Finset ι) (P : Measure Ω) :
    ∫⁻ ω, ⨆ R ∈ 𝓡 ω, fwerLoss N R ∂P = P {ω | ∃ R ∈ 𝓡 ω, ¬Disjoint R N} := by
  have hmeas : MeasurableSet {ω | ∃ R ∈ 𝓡 ω, ¬Disjoint R N} :=
    measurableSet_setOfPred.2 (Measurable.exists fun R ↦ h𝓡.mem.and measurable_const)
  rw [← lintegral_indicator_one hmeas]
  refine lintegral_congr fun ω ↦ ?_
  by_cases hω : ∃ R ∈ 𝓡 ω, ¬Disjoint R N
  · obtain ⟨R, hR, hRN⟩ := hω
    rw [Set.indicator_of_mem (show ω ∈ {ω | ∃ R ∈ 𝓡 ω, ¬Disjoint R N} from ⟨R, hR, hRN⟩),
      Pi.one_apply]
    refine le_antisymm (iSup₂_le fun R' _ ↦ ?_) (le_iSup₂_of_le R hR (by simp [hRN]))
    by_cases hR' : Disjoint R' N <;> simp [hR']
  · rw [Set.indicator_of_notMem hω]
    push Not at hω
    simp +contextual [hω]

end Losses

/-! ### The e-closure -/

/-- The e-closure of the statistics `e` for the loss `f` at level `α` [XSF+26, (2)]: the
rejection sets `R` with `f S R ≤ α * e S ω` for every set `S` of hypotheses. For an
e-collection, the loss of every member is at most `α` times the e-value of the true nulls. -/
def eClosure (f : Finset ι → Finset ι → ℝ≥0∞) (α : ℝ≥0∞) (e : Finset ι → Ω → ℝ≥0∞) (ω : Ω) :
    Set (Finset ι) :=
  {R | ∀ S, f S R ≤ α * e S ω}

variable {f : Finset ι → Finset ι → ℝ≥0∞} {α : ℝ≥0∞} {e : Finset ι → Ω → ℝ≥0∞} {ω : Ω}
  {R : Finset ι}

@[simp]
theorem mem_eClosure : R ∈ eClosure f α e ω ↔ ∀ S, f S R ≤ α * e S ω := Iff.rfl

/-- The empty rejection set belongs to every e-closure for a loss that vanishes on it. -/
theorem empty_mem_eClosure (hf : ∀ S, f S ∅ = 0) : ∅ ∈ eClosure f α e ω := by
  simp [hf]

/-- The e-closure of measurable statistics is a measurable candidate family. -/
theorem measurable_eClosure [Countable ι] (he : ∀ S, Measurable (e S)) :
    Measurable (eClosure f α e) :=
  measurable_set_iff.2 fun _ ↦ Measurable.forall fun S ↦
    measurableSet_setOfPred.1 (measurableSet_le measurable_const ((he S).const_mul α))

variable [Fintype ι] {H : ι → Set (Measure Ω)} {P : Measure Ω}

/-! ### True nulls and e-collections -/

/-- The true nulls under `P` of the hypotheses `H`: the indices `i` with `P ∈ H i`. -/
noncomputable def trueNulls (H : ι → Set (Measure Ω)) (P : Measure Ω) : Finset ι := by
  classical exact univ.filter fun i ↦ P ∈ H i

@[simp]
theorem mem_trueNulls {i : ι} : i ∈ trueNulls H P ↔ P ∈ H i := by
  classical simp [trueNulls]

/-- An e-collection for the hypotheses `H` [XSF+26, Definition 5]: a family of measurable
statistics `e S`, indexed by the sets `S` of hypotheses, with `e ∅ = 0`, such that the statistic
of the true nulls has expectation at most one under every probability measure `P`. Only the
statistics `e S` of the sets `S` that are the true nulls of some probability measure are
constrained: impossible combinations of true nulls are free. -/
structure IsECollection (e : Finset ι → Ω → ℝ≥0∞) (H : ι → Set (Measure Ω)) : Prop where
  /-- Each statistic is measurable. -/
  measurable (S : Finset ι) : Measurable (e S)
  /-- The statistic of the empty set of hypotheses vanishes. -/
  apply_empty : e ∅ = 0
  /-- The statistic of the true nulls has expectation at most one. -/
  lintegral_le_one (P : Measure Ω) [IsProbabilityMeasure P] :
    ∫⁻ ω, e (trueNulls H P) ω ∂P ≤ 1

/-- Statistics `e S` that are e-variables for the intersections `⋂ i ∈ S, H i` of the nonempty
sets of hypotheses form an e-collection [XSF+26, §4, after Definition 5]. -/
theorem IsECollection.of_isEVar {e : Finset ι → Ω → ℝ≥0∞}
    (he : ∀ S : Finset ι, S.Nonempty → IsEVar (e S) (⋂ i ∈ S, H i)) (he₀ : e ∅ = 0) :
    IsECollection e H where
  measurable S := by
    rcases S.eq_empty_or_nonempty with rfl | hS
    · rw [he₀]
      exact measurable_const
    · exact (he S hS).measurable
  apply_empty := he₀
  lintegral_le_one P _ := by
    rcases (trueNulls H P).eq_empty_or_nonempty with hN | hN
    · simp [hN, he₀]
    · simpa using (he _ hN).lintegral_le_measure_univ P (by simp)

/-- Measurable statistics below those of an e-collection, with `e' ∅ = 0`, form an
e-collection. -/
theorem IsECollection.of_le {e e' : Finset ι → Ω → ℝ≥0∞} (he : IsECollection e H)
    (he' : ∀ S, Measurable (e' S)) (he'₀ : e' ∅ = 0) (hle : ∀ S ω, e' S ω ≤ e S ω) :
    IsECollection e' H where
  measurable := he'
  apply_empty := he'₀
  lintegral_le_one P _ := (lintegral_mono (hle _)).trans (he.lintegral_le_one P)

/-! ### The post-hoc e-Closure Principle -/

/-- **The post-hoc e-Closure Principle**, validity [XSF+26, Theorem 48]: the e-closures of an
e-collection control a family of losses `f k` at levels `α k` simultaneously and post hoc. For
every probability measure, the expectation of the largest normalized loss `f k N R / α k` over the
indices `k` and the members `R` of the e-closures is at most one, so that the loss and the level
may be chosen after seeing the data. -/
theorem IsECollection.lintegral_iSup_div_le_one (he : IsECollection e H)
    (f : κ → Finset ι → Finset ι → ℝ≥0∞) (α : κ → ℝ≥0∞) (P : Measure Ω)
    [IsProbabilityMeasure P] :
    ∫⁻ ω, ⨆ k, ⨆ R ∈ eClosure (f k) (α k) e ω, f k (trueNulls H P) R / α k ∂P ≤ 1 :=
  (lintegral_mono fun _ ↦ iSup_le fun _ ↦ iSup₂_le fun _ hR ↦
    ENNReal.div_le_of_le_mul' (hR _)).trans (he.lintegral_le_one P)

/-- **The post-hoc e-Closure Principle**, completeness [XSF+26, Theorem 48]: a countable family
of measurable candidate families `𝓡 k`, for losses `f k` vanishing when there are no true nulls
and levels `α k ∉ {0, ∞}`, that controls the normalized losses simultaneously and post hoc, is
contained in the e-closures of one e-collection. -/
theorem exists_isECollection_of_lintegral_iSup_div_le_one [Countable κ]
    {f : κ → Finset ι → Finset ι → ℝ≥0∞} {α : κ → ℝ≥0∞} {𝓡 : κ → Ω → Set (Finset ι)}
    (hα₀ : ∀ k, α k ≠ 0) (hα : ∀ k, α k ≠ ∞) (hf : ∀ k R, f k ∅ R = 0)
    (h𝓡 : ∀ k, Measurable (𝓡 k))
    (hcontrol : ∀ (P : Measure Ω) [IsProbabilityMeasure P],
      ∫⁻ ω, ⨆ k, ⨆ R ∈ 𝓡 k ω, f k (trueNulls H P) R / α k ∂P ≤ 1) :
    ∃ e, IsECollection e H ∧ ∀ k ω, 𝓡 k ω ⊆ eClosure (f k) (α k) e ω := by
  -- The statistic of `S` is the largest normalized loss of the candidates when `S` is the set of
  -- true nulls [XSF+26, (25)].
  refine ⟨fun S ω ↦ ⨆ k, ⨆ R ∈ 𝓡 k ω, f k S R / α k, ⟨fun S ↦ ?_, ?_, hcontrol⟩, ?_⟩
  · -- A function of the finite family `𝓡 k ω` is measurable.
    exact Measurable.iSup fun k ↦
      (Measurable.of_discrete (f := fun t : Set (Finset ι) ↦ ⨆ R ∈ t, f k S R / α k)).comp (h𝓡 k)
  · ext ω
    simp [hf]
  · intro k ω R hR S
    calc f k S R = α k * (f k S R / α k) := (ENNReal.mul_div_cancel (hα₀ k) (hα k)).symm
      _ ≤ α k * ⨆ k, ⨆ R ∈ 𝓡 k ω, f k S R / α k := by
        gcongr
        exact le_iSup_of_le k (le_iSup₂_of_le R hR le_rfl)

/-! ### The e-Closure Principle -/

/-- **The e-Closure Principle**, validity [XSF+26, Theorem 6]: the e-closure of an e-collection
controls the loss simultaneously at level `α`, for every level `α`. -/
theorem IsECollection.lintegral_iSup_eClosure_le (he : IsECollection e H)
    (f : Finset ι → Finset ι → ℝ≥0∞) (α : ℝ≥0∞) (P : Measure Ω) [IsProbabilityMeasure P] :
    ∫⁻ ω, ⨆ R ∈ eClosure f α e ω, f (trueNulls H P) R ∂P ≤ α := by
  calc ∫⁻ ω, ⨆ R ∈ eClosure f α e ω, f (trueNulls H P) R ∂P
      ≤ ∫⁻ ω, α * e (trueNulls H P) ω ∂P :=
        lintegral_mono fun _ ↦ iSup₂_le fun _ hR ↦ hR _
    _ = α * ∫⁻ ω, e (trueNulls H P) ω ∂P := lintegral_const_mul α (he.measurable _)
    _ ≤ α := mul_le_of_le_one_right' (he.lintegral_le_one P)

/-- **The e-Closure Principle** [XSF+26, Theorem 6]: for a loss vanishing when there are no true
nulls and a level `α ∉ {0, ∞}`, a measurable candidate family controls the loss simultaneously at
level `α`, under every probability measure, exactly when it is contained in the e-closure of some
e-collection. -/
theorem forall_lintegral_iSup_le_iff_exists_isECollection {𝓡 : Ω → Set (Finset ι)}
    (hα₀ : α ≠ 0) (hα : α ≠ ∞) (hf : ∀ R, f ∅ R = 0) (h𝓡 : Measurable 𝓡) :
    (∀ (P : Measure Ω) [IsProbabilityMeasure P],
        ∫⁻ ω, ⨆ R ∈ 𝓡 ω, f (trueNulls H P) R ∂P ≤ α) ↔
      ∃ e, IsECollection e H ∧ ∀ ω, 𝓡 ω ⊆ eClosure f α e ω := by
  refine ⟨fun hcontrol ↦ ?_, fun ⟨e, he, h𝓡e⟩ P _ ↦ (lintegral_mono fun ω ↦
    biSup_mono fun R hR ↦ h𝓡e ω hR).trans (he.lintegral_iSup_eClosure_le f α P)⟩
  -- The case of a single loss and a single level of the post-hoc principle.
  have hcontrol' (P : Measure Ω) [IsProbabilityMeasure P] :
      ∫⁻ ω, ⨆ _ : Unit, ⨆ R ∈ 𝓡 ω, f (trueNulls H P) R / α ∂P ≤ 1 := calc
    ∫⁻ ω, ⨆ _ : Unit, ⨆ R ∈ 𝓡 ω, f (trueNulls H P) R / α ∂P
      ≤ ∫⁻ ω, (⨆ R ∈ 𝓡 ω, f (trueNulls H P) R) * α⁻¹ ∂P :=
        lintegral_mono fun _ ↦ iSup_le fun _ ↦ iSup₂_le fun R hR ↦
          (ENNReal.div_le_div_right (le_iSup₂_of_le (f := fun R _ ↦ f (trueNulls H P) R) R hR
            le_rfl) α).trans_eq (div_eq_mul_inv _ _)
    _ = (∫⁻ ω, ⨆ R ∈ 𝓡 ω, f (trueNulls H P) R ∂P) * α⁻¹ :=
        lintegral_mul_const' _ _ (ENNReal.inv_ne_top.2 hα₀)
    _ ≤ α * α⁻¹ := by gcongr; exact hcontrol P
    _ = 1 := ENNReal.mul_inv_cancel hα₀ hα
  obtain ⟨e, he, h𝓡e⟩ := exists_isECollection_of_lintegral_iSup_div_le_one (κ := Unit)
    (fun _ ↦ hα₀) (fun _ ↦ hα) (fun _ ↦ hf) (fun _ ↦ h𝓡) hcontrol'
  exact ⟨e, he, h𝓡e ()⟩

/-- **The e-Closure Principle for single rejection sets** [XSF+26, Corollary 7]: for a loss
vanishing when there are no true nulls and a level `α ∉ {0, ∞}`, a measurable rejection set
controls the loss at level `α`, under every probability measure, exactly when it belongs to the
e-closure of some e-collection. -/
theorem forall_lintegral_le_iff_exists_isECollection {R : Ω → Finset ι} (hα₀ : α ≠ 0)
    (hα : α ≠ ∞) (hf : ∀ R, f ∅ R = 0) (hR : Measurable R) :
    (∀ (P : Measure Ω) [IsProbabilityMeasure P], ∫⁻ ω, f (trueNulls H P) (R ω) ∂P ≤ α) ↔
      ∃ e, IsECollection e H ∧ ∀ ω, R ω ∈ eClosure f α e ω := by
  -- The candidate family `{R ω}`; a function of the finite set `R ω` is measurable.
  simpa using forall_lintegral_iSup_le_iff_exists_isECollection (H := H) hα₀ hα hf
    ((Measurable.of_discrete (f := fun R : Finset ι ↦ ({R} : Set (Finset ι)))).comp hR)

/-- **Simultaneous control is post-hoc control** [XSF+26, Lemma 4]: a measurable candidate family
with nonempty values controls a loss simultaneously at level `α`, under every probability measure,
exactly when every measurable data-dependent choice of one of its members controls it at level
`α`. -/
theorem forall_lintegral_iSup_le_iff_forall_lintegral_le {𝓡 : Ω → Set (Finset ι)}
    (h𝓡 : Measurable 𝓡) (hne : ∀ ω, (𝓡 ω).Nonempty) (f : Finset ι → Finset ι → ℝ≥0∞)
    (α : ℝ≥0∞) :
    (∀ (P : Measure Ω) [IsProbabilityMeasure P],
        ∫⁻ ω, ⨆ R ∈ 𝓡 ω, f (trueNulls H P) R ∂P ≤ α) ↔
      ∀ R : Ω → Finset ι, Measurable R → (∀ ω, R ω ∈ 𝓡 ω) →
        ∀ (P : Measure Ω) [IsProbabilityMeasure P], ∫⁻ ω, f (trueNulls H P) (R ω) ∂P ≤ α := by
  simp only [lintegral_biSup_eq_iSup_lintegral h𝓡 hne, iSup_le_iff]
  exact ⟨fun h R hR hR𝓡 P _ ↦ h P R hR hR𝓡, fun h P _ R hR hR𝓡 ↦ h R hR hR𝓡 P⟩

/-! ### The family-wise error rate and closed testing -/

section FamilyWise

/-- The closed testing rejection set [MPG76]: the hypotheses `i` such that the rejection event
`A S` of every set `S ∋ i` of hypotheses occurs at `ω`. -/
noncomputable def closedTesting (A : Finset ι → Set Ω) (ω : Ω) : Finset ι := by
  classical exact univ.filter fun i ↦ ∀ S, i ∈ S → ω ∈ A S

@[simp]
theorem mem_closedTesting {A : Finset ι → Set Ω} {i : ι} :
    i ∈ closedTesting A ω ↔ ∀ S, i ∈ S → ω ∈ A S := by
  classical simp [closedTesting]

/-- The closed testing rejection set of measurable rejection events is measurable. -/
theorem measurable_closedTesting {A : Finset ι → Set Ω} (hA : ∀ S, MeasurableSet (A S)) :
    Measurable (closedTesting A) :=
  measurable_finset_iff.2 fun i ↦ by
    simpa using Measurable.forall fun S ↦ measurable_const.imp (hA S).mem

/-- The closed testing rejection set depends only on the rejection events of the nonempty sets
of hypotheses. -/
theorem closedTesting_congr {A B : Finset ι → Set Ω} (h : ∀ S, S.Nonempty → A S = B S) :
    closedTesting A = closedTesting B := by
  ext ω i
  simp only [mem_closedTesting]
  exact forall_congr' fun S ↦ forall_congr' fun hi ↦ by rw [h S ⟨i, hi⟩]

variable [DecidableEq ι]

/-- For a level `α ∉ {0, ∞}`, the e-closure of `e` for the family-wise loss consists of the
subsets of the closed testing rejection set of the rejection events `{α⁻¹ ≤ e S}` [XSF+26, §4.1].
In particular it has a largest member. -/
theorem mem_eClosure_fwerLoss_iff (hα₀ : α ≠ 0) (hα : α ≠ ∞) :
    R ∈ eClosure fwerLoss α e ω ↔ R ⊆ closedTesting (fun S ↦ {ω | α⁻¹ ≤ e S ω}) ω := by
  have h1 (S : Finset ι) : 1 ≤ α * e S ω ↔ α⁻¹ ≤ e S ω :=
    (ENNReal.inv_le_iff_le_mul (fun _ ↦ hα₀) (fun h ↦ absurd h hα)).symm
  simp only [mem_eClosure, Finset.subset_iff, mem_closedTesting, Set.mem_ofPred_eq]
  refine ⟨fun h i hi S hS ↦ (h1 S).1 ?_, fun h S ↦ ?_⟩
  · simpa [not_disjoint_iff.2 ⟨i, hi, hS⟩] using h S
  · by_cases hRS : Disjoint R S
    · simp [hRS]
    · obtain ⟨i, hiR, hiS⟩ := not_disjoint_iff.1 hRS
      simpa [hRS] using (h1 S).2 (h hiR S hiS)

omit [DecidableEq ι] in
/-- **The e-Closure Principle for the family-wise error rate** [XSF+26, Theorem 12]: for a level
`α ∉ {0, ∞}`, a measurable candidate family controls the family-wise error rate simultaneously at
level `α`, under every probability measure, exactly when every member is contained in the closed
testing rejection set of the events `{α⁻¹ ≤ e S}` for some e-collection `e`, which can be chosen
with values in `{0, α⁻¹}`. -/
theorem forall_measure_exists_not_disjoint_le_iff_exists_isECollection
    {𝓡 : Ω → Set (Finset ι)} (hα₀ : α ≠ 0) (hα : α ≠ ∞) (h𝓡 : Measurable 𝓡) :
    (∀ (P : Measure Ω) [IsProbabilityMeasure P],
        P {ω | ∃ R ∈ 𝓡 ω, ¬Disjoint R (trueNulls H P)} ≤ α) ↔
      ∃ e, IsECollection e H ∧ (∀ S ω, e S ω = 0 ∨ e S ω = α⁻¹) ∧
        ∀ ω, ∀ R ∈ 𝓡 ω, R ⊆ closedTesting (fun S ↦ {ω | α⁻¹ ≤ e S ω}) ω := by
  classical
  simp_rw [← lintegral_iSup_fwerLoss h𝓡, forall_lintegral_iSup_le_iff_exists_isECollection hα₀ hα
    fwerLoss_empty_left h𝓡, Set.subset_def, mem_eClosure_fwerLoss_iff hα₀ hα]
  refine ⟨fun ⟨e, he, h𝓡e⟩ ↦ ?_, fun ⟨e, he, _, h𝓡e⟩ ↦ ⟨e, he, h𝓡e⟩⟩
  -- Thresholding `e S` at `α⁻¹` keeps the closed testing rejection set.
  have hα' : α⁻¹ ≠ 0 := ENNReal.inv_ne_zero.2 hα
  refine ⟨fun S ↦ {ω | α⁻¹ ≤ e S ω}.indicator fun _ ↦ α⁻¹, he.of_le (fun S ↦ ?_) ?_ ?_, ?_, ?_⟩
  · exact measurable_const.indicator (measurableSet_le measurable_const (he.measurable S))
  · ext ω
    simp [he.apply_empty, hα']
  · intro S ω
    by_cases h : α⁻¹ ≤ e S ω <;> simp [h]
  · intro S ω
    by_cases h : α⁻¹ ≤ e S ω <;> simp [h]
  · have hthr : (fun S ↦ {ω | α⁻¹ ≤ {ω | α⁻¹ ≤ e S ω}.indicator (fun _ ↦ α⁻¹) ω}) =
        fun S ↦ {ω | α⁻¹ ≤ e S ω} := by
      ext S ω
      by_cases h : α⁻¹ ≤ e S ω <;> simp [h, hα']
    simpa only [hthr] using h𝓡e

/-- The thresholded statistics `α⁻¹ * 𝟙 (A S)` of rejection events of level `α` for the true
nulls form an e-collection [XSF+26, Corollary 13]. -/
theorem isECollection_indicator {A : Finset ι → Set Ω} (hA : ∀ S, MeasurableSet (A S))
    (hlevel : ∀ (P : Measure Ω) [IsProbabilityMeasure P],
      (trueNulls H P).Nonempty → P (A (trueNulls H P)) ≤ α) :
    IsECollection (fun S ↦ if S = ∅ then 0 else (A S).indicator fun _ ↦ α⁻¹) H where
  measurable S := by
    split_ifs
    exacts [measurable_const, measurable_const.indicator (hA S)]
  apply_empty := by simp
  lintegral_le_one P _ := by
    rcases (trueNulls H P).eq_empty_or_nonempty with hN | hN
    · simp [hN]
    · simp only [hN.ne_empty, ↓reduceIte]
      rw [lintegral_indicator_const (hA _)]
      calc α⁻¹ * P (A (trueNulls H P)) ≤ α⁻¹ * α := by gcongr; exact hlevel P hN
        _ ≤ 1 := ENNReal.inv_mul_le_one α

/-- The closed testing rejection set and the e-closure for the family-wise loss
[XSF+26, Corollary 13]: for a level `α ∉ {0, ∞}`, the members of the e-closure of the thresholded
statistics `α⁻¹ * 𝟙 (A S)` are the subsets of the closed testing rejection set of the events
`A S`. -/
theorem mem_eClosure_fwerLoss_indicator_iff {A : Finset ι → Set Ω} (hα₀ : α ≠ 0) (hα : α ≠ ∞) :
    R ∈ eClosure fwerLoss α (fun S ↦ if S = ∅ then 0 else (A S).indicator fun _ ↦ α⁻¹) ω ↔
      R ⊆ closedTesting A ω := by
  have hα' : α⁻¹ ≠ 0 := ENNReal.inv_ne_zero.2 hα
  rw [mem_eClosure_fwerLoss_iff hα₀ hα]
  -- The rejection events `{α⁻¹ ≤ α⁻¹ * 𝟙 (A S)}` of the nonempty sets `S` are the events `A S`.
  suffices h : closedTesting (fun S ↦ {ω | α⁻¹ ≤
      (if S = ∅ then 0 else (A S).indicator fun _ ↦ α⁻¹ : Ω → ℝ≥0∞) ω}) = closedTesting A by
    rw [h]
  refine closedTesting_congr fun S hS ↦ ?_
  ext ω
  by_cases h : ω ∈ A S <;> simp [hS.ne_empty, h, hα']

omit [DecidableEq ι] in
/-- **The classical closure principle** [MPG76; XSF+26, Corollary 13]: for measurable rejection
events `A S` of level `α` for the true nulls, the closed testing rejection set rejects a true null
with probability at most `α`, under every probability measure. It is the largest member of the
e-closure, for the family-wise loss, of the e-collection `α⁻¹ * 𝟙 (A S)`. -/
theorem measure_not_disjoint_closedTesting_le {A : Finset ι → Set Ω} (hα₀ : α ≠ 0)
    (hα : α ≠ ∞) (hA : ∀ S, MeasurableSet (A S))
    (hlevel : ∀ (P : Measure Ω) [IsProbabilityMeasure P],
      (trueNulls H P).Nonempty → P (A (trueNulls H P)) ≤ α)
    (P : Measure Ω) [IsProbabilityMeasure P] :
    P {ω | ¬Disjoint (closedTesting A ω) (trueNulls H P)} ≤ α := by
  classical
  -- The candidate family of the subsets of the closed testing rejection set is contained in the
  -- e-closure of the e-collection `α⁻¹ * 𝟙 (A S)`.
  have h𝓡 : Measurable fun ω ↦ {R : Finset ι | R ⊆ closedTesting A ω} :=
    (Measurable.of_discrete (f := fun T : Finset ι ↦ {R : Finset ι | R ⊆ T})).comp
      (measurable_closedTesting hA)
  calc P {ω | ¬Disjoint (closedTesting A ω) (trueNulls H P)}
      ≤ P {ω | ∃ R ∈ {R : Finset ι | R ⊆ closedTesting A ω}, ¬Disjoint R (trueNulls H P)} :=
        measure_mono fun ω hω ↦ ⟨_, by simp, hω⟩
    _ = ∫⁻ ω, ⨆ R ∈ {R : Finset ι | R ⊆ closedTesting A ω}, fwerLoss (trueNulls H P) R ∂P :=
        (lintegral_iSup_fwerLoss h𝓡 _ P).symm
    _ ≤ α := (lintegral_mono fun ω ↦ biSup_mono fun R hR ↦
        (mem_eClosure_fwerLoss_indicator_iff hα₀ hα).2 hR).trans
          ((isECollection_indicator hA hlevel).lintegral_iSup_eClosure_le fwerLoss α P)

end FamilyWise

/-! ### The false discovery rate -/

/-- **The e-Closure Principle for the false discovery rate** [XSF+26, Theorem 14]: for a level
`α ∉ {0, ∞}`, a measurable candidate family controls the false discovery rate simultaneously at
level `α`, under every probability measure, exactly when it is contained in the e-closure of some
e-collection for the false discovery proportion. -/
theorem forall_lintegral_iSup_fdp_le_iff_exists_isECollection [DecidableEq ι]
    {𝓡 : Ω → Set (Finset ι)} (hα₀ : α ≠ 0) (hα : α ≠ ∞) (h𝓡 : Measurable 𝓡) :
    (∀ (P : Measure Ω) [IsProbabilityMeasure P],
        ∫⁻ ω, ⨆ R ∈ 𝓡 ω, fdp (trueNulls H P) R ∂P ≤ α) ↔
      ∃ e, IsECollection e H ∧ ∀ ω, 𝓡 ω ⊆ eClosure fdp α e ω :=
  forall_lintegral_iSup_le_iff_exists_isECollection hα₀ hα fdp_empty_left h𝓡

end ProbabilityTheory
