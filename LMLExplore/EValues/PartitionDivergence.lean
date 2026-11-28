/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.MeasureTheory.Measure.AddContent.YosidaHewitt
public import Statlib.EValues.RIPr
import LMLExplore.EValues.KLInf
import LMLExplore.MeasureTheory.Integral.BoundedMeasurable
import LMLExplore.MeasureTheory.Measure.Real
import TauCeti.MeasureTheory.SetAlgebra

/-!
# The divergence from a measure to a finitely additive measure

For a measure `R` and a set function `ν` on `Ω`, the divergence `H(R | ν)` is the supremum, over
the finite measurable partitions of `Ω` (measurable maps `f : Ω → Fin k`), of Statlib's
`klIntegral` from the image `R.map f` to the measure on `Fin k` with the masses `ν (f ⁻¹' {j})`.
For a finite measure `R` and an additive content `m` of finite mass on the measurable sets, it is
the divergence to the countably additive part `m_c` of `m`
(`MeasureTheory.countablyAdditivePart`): `H(R | m) = klIntegral R m_c`. The purely finitely
additive part of `m` adds nothing.

* The inequality `H(R | m) ≤ klIntegral R m_c` is data processing: the masses of `m` are at least
  those of `m_c`, `klIntegral` is antitone in its second argument, and it decreases along the
  measurable map `f`.
* For the converse, the variational formula for `klIntegral`, from Tau Ceti's variational formula
  for `klDiv`, reduces it to bounded measurable functions, which are approximated from below by
  step functions on a finite partition. The partition is then refined by a set `E` of small
  `R`-measure that carries all but a small part of the purely finitely additive part `m - m_c`
  (`MeasureTheory.exists_measurableSet_add_sub_countablyAdditivePart_lt`), with a very negative
  value on `E`.

## Main definitions

* `ProbabilityTheory.cellMeasure ν f`: the measure on the cells of a finite partition `f` with
  the masses of a set function `ν`.
* `ProbabilityTheory.partitionDivergence R ν`: the divergence `H(R | ν)` from a measure to a set
  function.

## Main statements

* `ProbabilityTheory.map_le_cellMeasure`: the image of a measure below `ν` is below the cell
  measure of `ν`.
* `ProbabilityTheory.partitionDivergence_le_klIntegral`: data processing,
  `H(R | ν) ≤ klIntegral R μ` for a finite measure `μ` below `ν` on the measurable sets.
* `ProbabilityTheory.partitionDivergence_eq_klIntegral_countablyAdditivePart`:
  `H(R | m) = klIntegral R m_c` [EVR26, Note 43, Section 3].

## Implementation notes

Divergences are Statlib's `klIntegral`, with no correction for the masses: on the measures of
mass at most one that the theory of e-values produces, it is the divergence that the duality
uses. The statements and proofs are adapted from `EValuesResearch/Results/Saturation.lean`
(commit `83205cb`) in the paper project `RemyDegenne/evalues_research`, rewritten on the API of
LMLExplore and generalized from a probability measure `R` and a set function of mass at most one
to finite ones; the inequality `H(R | m) ≤ klIntegral R m_c` is proved here.

## References

* [YH52] K. Yosida and E. Hewitt, *Finitely additive measures*, Trans. Amer. Math. Soc. 72
  (1952), 46–66.
* [EVR26] *Answers to open questions in e-values and anytime-valid inference*, notes 01 to 55 and
  the Lean library `EValuesResearch` of github.com/RemyDegenne/evalues_research, 2026; written and
  refereed by AI agents: Note 43, *Is the bipolar rate `KL_inf` to the i.i.d. saturation?*.
-/

public section

open MeasureTheory InformationTheory Set
open scoped ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-! ### The cell measure of a finite partition -/

/-- The measure on the cells of a finite partition `f : Ω → Fin k`, with the masses
`ν (f ⁻¹' {j})` of a set function `ν`. -/
noncomputable def cellMeasure (ν : Set Ω → ℝ≥0∞) {k : ℕ} (f : Ω → Fin k) : Measure (Fin k) :=
  Measure.sum fun j ↦ ν (f ⁻¹' {j}) • Measure.dirac j

variable {ν : Set Ω → ℝ≥0∞} {k : ℕ}

omit mΩ in
/-- The definition of the cell measure, as a sum of weighted Dirac masses. -/
theorem cellMeasure_def (ν : Set Ω → ℝ≥0∞) (f : Ω → Fin k) :
    cellMeasure ν f = Measure.sum fun j ↦ ν (f ⁻¹' {j}) • Measure.dirac j :=
  (rfl)

omit mΩ in
/-- The cell measure gives each cell `j` the mass `ν (f ⁻¹' {j})`. -/
@[simp]
theorem cellMeasure_apply_singleton (ν : Set Ω → ℝ≥0∞) (f : Ω → Fin k) (j : Fin k) :
    cellMeasure ν f {j} = ν (f ⁻¹' {j}) := by
  rw [cellMeasure_def, Measure.sum_smul_dirac_singleton]

omit mΩ in
/-- The cell measure is finite when every cell has finite mass. -/
theorem isFiniteMeasure_cellMeasure {f : Ω → Fin k} (hν : ∀ j, ν (f ⁻¹' {j}) ≠ ∞) :
    IsFiniteMeasure (cellMeasure ν f) := by
  refine ⟨?_⟩
  rw [cellMeasure_def, Measure.sum_apply _ .univ]
  simp only [smul_apply, measure_univ, smul_eq_mul, mul_one, tsum_fintype]
  exact ENNReal.sum_lt_top.2 fun j _ ↦ (hν j).lt_top

/-- For a measurable partition `f` and a measure `μ` below `ν` on the measurable sets, the image
`μ.map f` is below the cell measure of `ν`. -/
theorem map_le_cellMeasure {μ : Measure Ω} {f : Ω → Fin k} (hf : Measurable f)
    (hμν : ∀ s, MeasurableSet s → μ s ≤ ν s) :
    μ.map f ≤ cellMeasure ν f := by
  conv_lhs => rw [← Measure.sum_smul_dirac (μ.map f)]
  refine Measure.le_iff.2 fun A hA ↦ ?_
  rw [cellMeasure_def, Measure.sum_apply _ hA, Measure.sum_apply _ hA]
  refine tsum_le_tsum fun j ↦ ?_
  simp only [smul_apply, smul_eq_mul]
  rw [Measure.map_apply hf (measurableSet_singleton j)]
  exact mul_le_mul_left (hμν _ (hf (measurableSet_singleton j))) _

/-! ### The divergence from a measure to a set function -/

/-- The divergence `H(R | ν)` from a measure `R` to a set function `ν`: the supremum, over the
finite measurable partitions of `Ω` (measurable maps `f : Ω → Fin k`), of the divergence
`klIntegral` from the image `R.map f` to the cell measure `cellMeasure ν f`, with the masses
`ν (f ⁻¹' {j})`. For finite measures `R` and `ν`, it is at most `klIntegral R ν`
(`ProbabilityTheory.partitionDivergence_le_klIntegral`). -/
noncomputable def partitionDivergence (R : Measure Ω) (ν : Set Ω → ℝ≥0∞) : EReal :=
  ⨆ (k : ℕ) (f : Ω → Fin k) (_ : Measurable f), klIntegral (R.map f) (cellMeasure ν f)

/-- The definition of `H(R | ν)`, as a supremum over the finite measurable partitions. -/
theorem partitionDivergence_def (R : Measure Ω) (ν : Set Ω → ℝ≥0∞) :
    partitionDivergence R ν =
      ⨆ (k : ℕ) (f : Ω → Fin k) (_ : Measurable f), klIntegral (R.map f) (cellMeasure ν f) :=
  (rfl)

/-- The divergence on one finite measurable partition is at most `H(R | ν)`. -/
theorem klIntegral_le_partitionDivergence (R : Measure Ω) {f : Ω → Fin k} (hf : Measurable f) :
    klIntegral (R.map f) (cellMeasure ν f) ≤ partitionDivergence R ν :=
  le_iSup₂_of_le (f := fun (k : ℕ) (f : Ω → Fin k) ↦ ⨆ (_ : Measurable f),
    klIntegral (R.map f) (cellMeasure ν f)) k f (le_iSup_of_le hf le_rfl)

/-- **Data processing** for the divergence to a set function: for finite measures `R` and `μ`
and a set function `ν` that is finite and at least `μ` on the measurable sets,
`H(R | ν) ≤ klIntegral R μ`. In particular `H(R | μ) ≤ klIntegral R μ`. -/
theorem partitionDivergence_le_klIntegral (R : Measure Ω) [IsFiniteMeasure R] {μ : Measure Ω}
    [IsFiniteMeasure μ] (hμν : ∀ s, MeasurableSet s → μ s ≤ ν s)
    (hν : ∀ s, MeasurableSet s → ν s ≠ ∞) :
    partitionDivergence R ν ≤ klIntegral R μ := by
  -- on each partition, `klIntegral` is antitone in its second argument and decreases along `f`
  refine iSup₂_le fun k f ↦ iSup_le fun hf ↦ ?_
  have := isFiniteMeasure_cellMeasure fun j ↦ hν _ (hf (measurableSet_singleton j))
  exact (klIntegral_anti_right (map_le_cellMeasure hf hμν)).trans (klIntegral_map_le hf)

/-! ### Finite measurable partitions -/

open Classical in
/-- The refinement of a finite partition `π` by a set `E`: the last cell is `E`, and the other
cells are those of `π` outside `E`. -/
private noncomputable def refineBy (π : Ω → Fin k) (E : Set Ω) : Ω → Fin (k + 1) :=
  fun x ↦ if x ∈ E then Fin.last k else (π x).castSucc

/-- The refinement of a measurable partition by a measurable set is measurable. -/
private lemma measurable_refineBy {π : Ω → Fin k} (hπ : Measurable π) {E : Set Ω}
    (hE : MeasurableSet E) : Measurable (refineBy π E) := by
  classical
  exact Measurable.ite hE measurable_const ((measurable_of_finite Fin.castSucc).comp hπ)

omit mΩ in
/-- The cell `j` of the refinement is the cell `j` of `π` outside `E`. -/
private lemma refineBy_preimage_castSucc (π : Ω → Fin k) (E : Set Ω) (j : Fin k) :
    refineBy π E ⁻¹' {j.castSucc} = π ⁻¹' {j} ∩ Eᶜ := by
  ext x
  by_cases hx : x ∈ E
  · simp [refineBy, hx, (Fin.castSucc_lt_last j).ne']
  · simp [refineBy, hx]

omit mΩ in
/-- The last cell of the refinement is `E`. -/
private lemma refineBy_preimage_last (π : Ω → Fin k) (E : Set Ω) :
    refineBy π E ⁻¹' {Fin.last k} = E := by
  ext x
  by_cases hx : x ∈ E
  · simp [refineBy, hx]
  · simp [refineBy, hx, (Fin.castSucc_lt_last _).ne]

/-- The choice of constants for the bound on a finite partition: for `c, N ≥ 0` and `η > 0`,
there are `M ≥ 0` and `ε > 0` with `exp (-M) c ≤ η / 2`, and `(N + M) a + exp N p ≤ η / 2`
whenever `a, p ≥ 0` and `a + p < ε`. -/
private lemma exists_exp_neg_mul_le_and_add_mul_le {c N η : ℝ} (hc0 : 0 ≤ c) (hN : 0 ≤ N)
    (hη : 0 < η) :
    ∃ M ε : ℝ, 0 ≤ M ∧ 0 < ε ∧ Real.exp (-M) * c ≤ η / 2 ∧
      ∀ a p : ℝ, 0 ≤ a → 0 ≤ p → a + p < ε → (N + M) * a + Real.exp N * p ≤ η / 2 := by
  set M : ℝ := max (Real.log (2 * (c + 1) / η)) 0 with hM
  have hM0 : 0 ≤ M := le_max_right _ _
  set K : ℝ := N + M + Real.exp N + 1 with hK
  have hK0 : 0 < K := by positivity
  refine ⟨M, η / (2 * K), hM0, by positivity, ?_, fun a p ha hp hsmall ↦ ?_⟩
  · have h1 : Real.exp (-M) ≤ η / (2 * (c + 1)) := by
      calc Real.exp (-M) ≤ Real.exp (-Real.log (2 * (c + 1) / η)) :=
            Real.exp_le_exp.2 (neg_le_neg (le_max_left _ _))
        _ = η / (2 * (c + 1)) := by rw [Real.exp_neg, Real.exp_log (by positivity), inv_div]
    calc Real.exp (-M) * c ≤ η / (2 * (c + 1)) * c := mul_le_mul_of_nonneg_right h1 hc0
      _ ≤ η / 2 := by
        rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
  · have h1 : (N + M) * a + Real.exp N * p ≤ K * (a + p) := by
      have := mul_nonneg (by positivity : (0 : ℝ) ≤ Real.exp N + 1) ha
      have := mul_nonneg (by positivity : (0 : ℝ) ≤ N + M + 1) hp
      nlinarith
    have h2 : K * (a + p) ≤ K * (η / (2 * K)) := mul_le_mul_of_nonneg_left hsmall.le hK0.le
    have h3 : K * (η / (2 * K)) = η / 2 := by field_simp
    linarith

/-! ### The divergence to a finitely additive measure -/

variable {m : AddContent ℝ≥0∞ {s : Set Ω | MeasurableSet s}}

/-- **The bound on a finite partition.** For a finite measure `R`, an additive content `m` of
finite mass on the measurable sets with countably additive part `m_c`, a finite measurable
partition `π`, values `h j` with `|h j| ≤ N` and `η > 0`,
`∑ j, h j R(π = j) - ∑ j, exp (h j) m_c(π = j) + R univ - η ≤ H(R | m)`. -/
private lemma sum_sub_sum_exp_add_sub_le_partitionDivergence (R : Measure Ω) [IsFiniteMeasure R]
    (hm : m univ ≠ ∞) {π : Ω → Fin k} (hπ : Measurable π) (h : Fin k → ℝ) {N : ℝ}
    (hN : 0 ≤ N) (hhN : ∀ j, |h j| ≤ N) {η : ℝ} (hη : 0 < η) :
    ((∑ j, h j * R.real (π ⁻¹' {j}) -
        ∑ j, Real.exp (h j) * (countablyAdditivePart m).real (π ⁻¹' {j}) + R.real univ - η :
          ℝ) : EReal) ≤ partitionDivergence R m := by
  -- the partition is refined by a set `E` of small `R`-measure that carries all but a small part
  -- of `m - m_c`, with the value `-M` on `E` for a large `M`; the variational lower bound for
  -- `klIntegral` on the refined partition gives the inequality
  set μc := countablyAdditivePart m with hμc
  have : IsFiniteMeasure μc := isFiniteMeasure_countablyAdditivePart hm
  have hmfin (A : Set Ω) (hA : MeasurableSet A) : m A ≠ ⊤ :=
    AddContent.apply_ne_top_of_univ_ne_top hm hA
  have hμcm (A : Set Ω) (hA : MeasurableSet A) : μc A ≤ m A := countablyAdditivePart_apply_le m hA
  -- the constants
  obtain ⟨M, ε, hM0, hε0, hexpM, hcomb⟩ :=
    exists_exp_neg_mul_le_and_add_mul_le ENNReal.toReal_nonneg hN hη (c := (m univ).toReal)
  -- a set `E` of small `R`-measure that carries all but a small part of `m - μc`
  obtain ⟨E, hE, hEε⟩ :=
    exists_measurableSet_add_sub_countablyAdditivePart_lt hm R (ENNReal.ofReal_pos.2 hε0)
  set aE := R.real E with haE
  set pE := (m Eᶜ).toReal - μc.real Eᶜ with hpE
  have hpE0 : 0 ≤ pE := by
    rw [hpE, sub_nonneg, measureReal_def]
    exact ENNReal.toReal_mono (hmfin _ hE.compl) (hμcm _ hE.compl)
  have haE0 : 0 ≤ aE := measureReal_nonneg
  have hsmall : aE + pE < ε := by
    have htop : m Eᶜ - μc Eᶜ ≠ ⊤ := ne_top_of_le_ne_top (hmfin _ hE.compl) tsub_le_self
    have h2 := ENNReal.toReal_lt_of_lt_ofReal hEε
    rw [ENNReal.toReal_add (measure_ne_top _ _) htop,
      ENNReal.toReal_sub_of_le (hμcm _ hE.compl) (hmfin _ hE.compl)] at h2
    simpa only [haE, hpE, measureReal_def] using h2
  have hcomb' := hcomb aE pE haE0 hpE0 hsmall
  -- the refined partition, with the values `h` off `E` and `-M` on `E`
  have hπ'm := measurable_refineBy hπ hE
  set h' : Fin (k + 1) → ℝ := Fin.snoc h (-M) with hh'
  have : IsFiniteMeasure (cellMeasure m (refineBy π E)) :=
    isFiniteMeasure_cellMeasure fun i ↦ hmfin _ (hπ'm (measurableSet_singleton i))
  -- the variational lower bound on the refined partition
  have hlow := integral_sub_integral_exp_add_le_klIntegral (μ := R.map (refineBy π E))
    (ν := cellMeasure m (refineBy π E)) (f := h') Integrable.of_finite Integrable.of_finite
  have e1 : ∑ i, (R.map (refineBy π E)).real {i} • h' i =
      ∑ i, h' i * R.real (refineBy π E ⁻¹' {i}) :=
    Finset.sum_congr rfl fun i _ ↦ by
      rw [smul_eq_mul, mul_comm, map_measureReal_apply hπ'm (measurableSet_singleton i)]
  have e2 : ∑ i, (cellMeasure m (refineBy π E)).real {i} • Real.exp (h' i) =
      ∑ i, Real.exp (h' i) * (m (refineBy π E ⁻¹' {i})).toReal :=
    Finset.sum_congr rfl fun i _ ↦ by
      rw [smul_eq_mul, mul_comm, measureReal_def, cellMeasure_apply_singleton]
  rw [integral_fintype Integrable.of_finite, integral_fintype Integrable.of_finite, e1, e2,
    map_measureReal_apply hπ'm .univ, preimage_univ] at hlow
  refine le_trans ?_ (hlow.trans (klIntegral_le_partitionDivergence R hπ'm))
  rw [EReal.coe_le_coe_iff, Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
  simp only [hh', Fin.snoc_castSucc, Fin.snoc_last, refineBy_preimage_castSucc,
    refineBy_preimage_last]
  -- the bounds on the cells
  have hsplit (j : Fin k) :
      R.real (π ⁻¹' {j}) = R.real (π ⁻¹' {j} ∩ Eᶜ) + R.real (π ⁻¹' {j} ∩ E) := by
    rw [add_comm, ← measureReal_inter_add_sdiff (s := π ⁻¹' {j}) hE, Set.sdiff_eq]
  have hb1 : ∑ j, h j * R.real (π ⁻¹' {j}) ≤ ∑ j, h j * R.real (π ⁻¹' {j} ∩ Eᶜ) + N * aE := by
    have : ∑ j, h j * R.real (π ⁻¹' {j} ∩ E) ≤ N * aE := by
      calc ∑ j, h j * R.real (π ⁻¹' {j} ∩ E) ≤ ∑ j, N * R.real (π ⁻¹' {j} ∩ E) :=
            Finset.sum_le_sum fun j _ ↦
              mul_le_mul_of_nonneg_right ((le_abs_self _).trans (hhN j)) measureReal_nonneg
        _ = N * aE := by
          rw [← Finset.mul_sum, LMLExplore.sum_measureReal_preimage_singleton_inter R hπ E]
    calc ∑ j, h j * R.real (π ⁻¹' {j})
        = ∑ j, h j * R.real (π ⁻¹' {j} ∩ Eᶜ) + ∑ j, h j * R.real (π ⁻¹' {j} ∩ E) := by
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun j _ ↦ by rw [hsplit j, mul_add]
      _ ≤ _ := add_le_add le_rfl this
  have hb2 : ∑ j, Real.exp (h j) * (m (π ⁻¹' {j} ∩ Eᶜ)).toReal ≤
      ∑ j, Real.exp (h j) * μc.real (π ⁻¹' {j}) + Real.exp N * pE := by
    have hterm (j : Fin k) : Real.exp (h j) * (m (π ⁻¹' {j} ∩ Eᶜ)).toReal ≤
        Real.exp (h j) * μc.real (π ⁻¹' {j}) + Real.exp N *
          ((m (π ⁻¹' {j} ∩ Eᶜ)).toReal - μc.real (π ⁻¹' {j} ∩ Eᶜ)) := by
      have hfib : MeasurableSet (π ⁻¹' {j} ∩ Eᶜ) := (hπ (measurableSet_singleton j)).inter hE.compl
      have h1 : μc.real (π ⁻¹' {j} ∩ Eᶜ) ≤ μc.real (π ⁻¹' {j}) :=
        measureReal_mono inter_subset_left
      have h2 : μc.real (π ⁻¹' {j} ∩ Eᶜ) ≤ (m (π ⁻¹' {j} ∩ Eᶜ)).toReal := by
        rw [measureReal_def]
        exact ENNReal.toReal_mono (hmfin _ hfib) (hμcm _ hfib)
      have h3 : Real.exp (h j) ≤ Real.exp N := Real.exp_le_exp.2 ((le_abs_self _).trans (hhN j))
      calc Real.exp (h j) * (m (π ⁻¹' {j} ∩ Eᶜ)).toReal
          = Real.exp (h j) * μc.real (π ⁻¹' {j} ∩ Eᶜ) + Real.exp (h j) *
            ((m (π ⁻¹' {j} ∩ Eᶜ)).toReal - μc.real (π ⁻¹' {j} ∩ Eᶜ)) := by ring
        _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le)
            (mul_le_mul_of_nonneg_right h3 (sub_nonneg.2 h2))
    calc ∑ j, Real.exp (h j) * (m (π ⁻¹' {j} ∩ Eᶜ)).toReal
        ≤ ∑ j, (Real.exp (h j) * μc.real (π ⁻¹' {j}) + Real.exp N *
          ((m (π ⁻¹' {j} ∩ Eᶜ)).toReal - μc.real (π ⁻¹' {j} ∩ Eᶜ))) :=
          Finset.sum_le_sum fun j _ ↦ hterm j
      _ = _ := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib,
            sum_toReal_addContent_preimage_singleton_inter hm hπ hE.compl,
            LMLExplore.sum_measureReal_preimage_singleton_inter μc hπ Eᶜ]
  have hb3 : Real.exp (-M) * (m E).toReal ≤ η / 2 :=
    (mul_le_mul_of_nonneg_left (ENNReal.toReal_mono hm
      (addContent_mono isSetRing_measurableSet.isSetSemiring hE .univ (subset_univ E)))
      (Real.exp_pos _).le).trans hexpM
  nlinarith [hb1, hb2, hb3, hcomb', mul_nonneg hM0 haE0]

/-- **The bound for a bounded measurable function.** For a finite measure `R`, an additive
content `m` of finite mass on the measurable sets with countably additive part `m_c` and a
bounded measurable `g`, `∫ g dR - ∫ exp g dm_c + R univ ≤ H(R | m)`. -/
private lemma integral_sub_integral_exp_add_le_partitionDivergence (R : Measure Ω)
    [IsFiniteMeasure R] (hm : m univ ≠ ∞) {g : Ω → ℝ} (hg : Measurable g) {N₀ : ℝ}
    (hgN₀ : ∀ x, |g x| ≤ N₀) :
    ((∫ x, g x ∂R - ∫ x, Real.exp (g x) ∂(countablyAdditivePart m) + R.real univ : ℝ) :
      EReal) ≤ partitionDivergence R m := by
  set μc := countablyAdditivePart m with hμc
  have : IsFiniteMeasure μc := isFiniteMeasure_countablyAdditivePart hm
  obtain ⟨N, hN, hgN⟩ : ∃ N, 0 ≤ N ∧ ∀ x, |g x| ≤ N :=
    ⟨max N₀ 0, le_max_right _ _, fun x ↦ (hgN₀ x).trans (le_max_left _ _)⟩
  have hRu : 0 ≤ R.real univ := measureReal_nonneg
  have key (η : ℝ) (hη : 0 < η) :
      ((∫ x, g x ∂R - ∫ x, Real.exp (g x) ∂μc + R.real univ - η : ℝ) : EReal) ≤
        partitionDivergence R m := by
    set δ := η / (2 * (R.real univ + 1)) with hδ
    have hδ0 : 0 < δ := div_pos hη (by linarith)
    have hRδ : R.real univ * δ ≤ η / 2 := by
      rw [hδ, ← mul_div_assoc, div_le_div_iff₀ (by linarith) (by norm_num)]
      nlinarith
    -- approximate `g` from below by a step function `h ∘ π`
    obtain ⟨n, π, h, hπm, hgh, hhN⟩ := LMLExplore.exists_measurable_fin_step_le hg hgN hδ0
    have hhπm : Measurable fun x ↦ h (π x) := (measurable_of_finite h).comp hπm
    have h1 : ∫ x, g x ∂R ≤ ∑ j, h j * R.real (π ⁻¹' {j}) + R.real univ * δ := by
      have hmono : ∫ x, g x ∂R ≤ ∫ x, (h (π x) + δ) ∂R :=
        integral_mono (LMLExplore.integrable_of_abs_le hg hgN R)
          ((LMLExplore.integrable_of_abs_le hhπm (fun x ↦ hhN (π x)) R).add (integrable_const δ))
          (fun x ↦ by linarith [(hgh x).1])
      rw [integral_add (LMLExplore.integrable_of_abs_le hhπm (fun x ↦ hhN (π x)) R)
        (integrable_const _), integral_const, smul_eq_mul,
        LMLExplore.integral_comp_eq_sum R hπm h] at hmono
      linarith
    have h2 : ∑ j, Real.exp (h j) * μc.real (π ⁻¹' {j}) ≤ ∫ x, Real.exp (g x) ∂μc := by
      rw [← LMLExplore.integral_comp_eq_sum μc hπm fun j ↦ Real.exp (h j)]
      exact integral_mono (LMLExplore.integrable_exp_of_abs_le hhπm (fun x ↦ hhN (π x)) μc)
        (LMLExplore.integrable_exp_of_abs_le hg hgN μc) fun x ↦ Real.exp_le_exp.2 (hgh x).2
    have hstep := sum_sub_sum_exp_add_sub_le_partitionDivergence R hm hπm h
      (by positivity : 0 ≤ N + δ) hhN (half_pos hη)
    refine le_trans ?_ hstep
    rw [EReal.coe_le_coe_iff]
    linarith
  -- conclude, letting `η → 0`
  refine EReal.ge_of_forall_gt_iff_ge.1 fun z hz ↦ ?_
  have := key _ (sub_pos.2 (EReal.coe_lt_coe_iff.1 hz))
  rwa [sub_sub_cancel] at this

/-- **The countably additive part carries the divergence** [EVR26, Note 43, Section 3]: for a
finite measure `R` and an additive content `m` of finite mass on the measurable sets,
`klIntegral R m_c ≤ H(R | m)`, with `m_c` the countably additive part of `m`. -/
theorem klIntegral_countablyAdditivePart_le_partitionDivergence (R : Measure Ω)
    [IsFiniteMeasure R] (hm : m univ ≠ ∞) :
    klIntegral R (countablyAdditivePart m) ≤ partitionDivergence R m := by
  -- the variational formula for `klIntegral` reduces it to bounded measurable functions
  have := isFiniteMeasure_countablyAdditivePart hm
  rw [klIntegral_eq_iSup_integral_sub_integral_exp_add]
  exact iSup₂_le fun g hg ↦ iSup_le fun ⟨N, hgN⟩ ↦
    integral_sub_integral_exp_add_le_partitionDivergence R hm hg hgN

/-- **The divergence to a finitely additive measure is the divergence to its countably additive
part** [EVR26, Note 43, Section 3]: for a finite measure `R` and an additive content `m` of finite
mass on the measurable sets, `H(R | m) = klIntegral R m_c`, with `m_c` the countably additive part
of `m`. The purely finitely additive part `m - m_c` of the Yosida–Hewitt decomposition [YH52]
adds nothing. -/
theorem partitionDivergence_eq_klIntegral_countablyAdditivePart (R : Measure Ω)
    [IsFiniteMeasure R] (hm : m univ ≠ ∞) :
    partitionDivergence R m = klIntegral R (countablyAdditivePart m) := by
  have := isFiniteMeasure_countablyAdditivePart hm
  exact le_antisymm (partitionDivergence_le_klIntegral R
    (fun s hs ↦ countablyAdditivePart_apply_le m hs)
    fun s hs ↦ AddContent.apply_ne_top_of_univ_ne_top hm hs)
    (klIntegral_countablyAdditivePart_le_partitionDivergence R hm)

end ProbabilityTheory
