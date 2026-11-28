/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.MeasureTheory.Measure.AddContent.YosidaHewitt
public import Statlib.EValues.RIPr
import LMLExplore.EValues.KLInf
import Mathlib.MeasureTheory.Function.Floor
import TauCeti.InformationTheory.KullbackLeibler.Variational
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

* `ProbabilityTheory.partitionDivergence R ν`: the divergence `H(R | ν)` from a measure to a set
  function.

## Main statements

* `ProbabilityTheory.klIntegral_eq_iSup_integral_sub_integral_exp_add`: the variational formula for
  `klIntegral`, on finite measures, and `ProbabilityTheory.klIntegral_anti_right`: the
  antitonicity of `klIntegral` in its second argument.
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

/-! ### The variational formula for `klIntegral` -/

/-- A bounded measurable function is integrable under a finite measure, and so is its
exponential. -/
private lemma integrable_and_integrable_exp {μ : Measure Ω} [IsFiniteMeasure μ] {f : Ω → ℝ}
    (hf : Measurable f) {C : ℝ} (hC : ∀ x, |f x| ≤ C) :
    Integrable f μ ∧ Integrable (fun x ↦ Real.exp (f x)) μ :=
  ⟨.of_bound hf.aestronglyMeasurable C (ae_of_all _ hC),
    .of_bound hf.exp.aestronglyMeasurable (Real.exp C) (ae_of_all _ fun x ↦ by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.2 (le_of_abs_le (hC x)))⟩

/-- **The variational lower bound for `klIntegral`**: for finite measures `μ` and `ν` and a
function `f` integrable under `μ` with `exp ∘ f` integrable under `ν`,
`∫ f dμ - ∫ exp f dν + μ univ ≤ klIntegral μ ν`. It is Tau Ceti's lower bound for `klDiv`
(`TauCeti.ofReal_integral_sub_integral_exp_sub_one_le_klDiv`), corrected by the masses. -/
theorem integral_sub_integral_exp_add_le_klIntegral {μ ν : Measure Ω} [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] {f : Ω → ℝ} (hf : Integrable f μ)
    (hef : Integrable (fun x ↦ Real.exp (f x)) ν) :
    ((∫ x, f x ∂μ - ∫ x, Real.exp (f x) ∂ν + μ.real univ : ℝ) : EReal) ≤ klIntegral μ ν := by
  have h := TauCeti.ofReal_integral_sub_integral_exp_sub_one_le_klDiv hf hef
  rw [integral_sub hef (integrable_const 1), integral_const, smul_eq_mul, mul_one] at h
  rw [klIntegral_eq_klDiv_add_sub]
  rcases eq_or_ne (klDiv μ ν) ∞ with hK | hK
  · rw [hK, EReal.coe_ennreal_top, EReal.top_add_coe, EReal.top_sub_coe]
    exact le_top
  rw [← ENNReal.ofReal_toReal hK, ENNReal.ofReal_le_ofReal_iff ENNReal.toReal_nonneg] at h
  rw [← ENNReal.ofReal_toReal hK, EReal.coe_ennreal_ofReal, max_eq_left ENNReal.toReal_nonneg,
    ← EReal.coe_add, ← EReal.coe_sub, EReal.coe_le_coe_iff]
  linarith

/-- **The variational formula for `klIntegral`**: for finite measures `μ` and `ν`,
`klIntegral μ ν` is the supremum of `∫ f dμ - ∫ exp f dν + μ univ` over the bounded measurable
functions `f`. It is Tau Ceti's variational formula for `klDiv`
(`TauCeti.klDiv_eq_iSup_integral_sub_integral_exp_sub_one`), corrected by the masses. -/
theorem klIntegral_eq_iSup_integral_sub_integral_exp_add (μ ν : Measure Ω) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] :
    klIntegral μ ν = ⨆ (f : Ω → ℝ) (_ : Measurable f) (_ : ∃ C, ∀ x, |f x| ≤ C),
      ((∫ x, f x ∂μ - ∫ x, Real.exp (f x) ∂ν + μ.real univ : ℝ) : EReal) := by
  refine le_antisymm ?_ (iSup₂_le fun f hf ↦ iSup_le fun ⟨C, hC⟩ ↦
    integral_sub_integral_exp_add_le_klIntegral (integrable_and_integrable_exp hf hC).1
      (integrable_and_integrable_exp hf hC).2)
  rw [klIntegral_eq_klDiv_add_sub, TauCeti.klDiv_eq_iSup_integral_sub_integral_exp_sub_one]
  set Y := ⨆ (f : Ω → ℝ) (_ : Measurable f) (_ : ∃ C, ∀ x, |f x| ≤ C),
    ENNReal.ofReal (∫ x, f x ∂μ - ∫ x, (Real.exp (f x) - 1) ∂ν) with hY
  refine le_of_forall_lt_imp_le_of_dense fun c hc ↦ ?_
  induction c using EReal.rec with
  | bot => exact bot_le
  | top => exact absurd hc not_top_lt
  | coe t =>
    obtain ⟨g, hg, N, hgN, htg⟩ : ∃ g : Ω → ℝ, Measurable g ∧ ∃ N, (∀ x, |g x| ≤ N) ∧
        t < ∫ x, g x ∂μ - ∫ x, Real.exp (g x) ∂ν + μ.real univ := by
      by_cases ht : t - μ.real univ + ν.real univ < 0
      · refine ⟨fun _ ↦ 0, measurable_const, 0, fun _ ↦ by simp, ?_⟩
        simp only [integral_zero, Real.exp_zero, integral_const, smul_eq_mul, mul_one]
        linarith
      replace ht := not_lt.1 ht
      have hlt : ENNReal.ofReal (t - μ.real univ + ν.real univ) < Y := by
        rcases eq_or_ne Y ⊤ with hYt | hYt
        · rw [hYt]
          exact ENNReal.ofReal_lt_top
        rw [ENNReal.ofReal_lt_iff_lt_toReal ht hYt]
        rw [← EReal.coe_ennreal_toReal hYt] at hc
        have hc' : ((t : ℝ) : EReal) < ((Y.toReal + μ.real univ - ν.real univ : ℝ) : EReal) := by
          rw [EReal.coe_sub, EReal.coe_add]
          exact hc
        rw [EReal.coe_lt_coe_iff] at hc'
        linarith
      obtain ⟨f, hlt₁⟩ := lt_iSup_iff.1 hlt
      obtain ⟨hf, hlt₂⟩ := lt_iSup_iff.1 hlt₁
      obtain ⟨⟨C, hC⟩, hlt₃⟩ := lt_iSup_iff.1 hlt₂
      refine ⟨f, hf, C, hC, ?_⟩
      have h := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ht).1 hlt₃
      rw [integral_sub (integrable_and_integrable_exp hf hC).2 (integrable_const 1),
        integral_const, smul_eq_mul, mul_one] at h
      linarith
    exact (EReal.coe_le_coe_iff.2 htg.le).trans
      (le_iSup₂_of_le g hg (le_iSup_of_le ⟨N, hgN⟩ le_rfl))

/-- `klIntegral μ ν` is antitone in `ν`, on finite measures: a larger reference measure gives a
smaller divergence. -/
theorem klIntegral_anti_right {μ ν ν' : Measure Ω} [IsFiniteMeasure μ]
    [IsFiniteMeasure ν'] (h : ν ≤ ν') :
    klIntegral μ ν' ≤ klIntegral μ ν := by
  have : IsFiniteMeasure ν := isFiniteMeasure_of_le ν' h
  rw [klIntegral_eq_iSup_integral_sub_integral_exp_add,
    klIntegral_eq_iSup_integral_sub_integral_exp_add]
  refine iSup₂_mono fun f hf ↦ iSup_mono fun ⟨C, hC⟩ ↦ EReal.coe_le_coe_iff.2 ?_
  have := integral_mono_measure h (ae_of_all _ fun x ↦ (Real.exp_pos (f x)).le)
    (integrable_and_integrable_exp hf hC).2
  linarith

/-! ### The divergence from a measure to a set function -/

/-- The divergence `H(R | ν)` from a measure `R` to a set function `ν`: the supremum, over the
finite measurable partitions of `Ω` (measurable maps `f : Ω → Fin k`), of the divergence
`klIntegral` from the image `R.map f` to the measure on `Fin k` with the masses `ν (f ⁻¹' {j})`.
For a finite measure `ν` it is at most `klIntegral R ν`
(`ProbabilityTheory.partitionDivergence_le_klIntegral`). -/
noncomputable def partitionDivergence (R : Measure Ω) (ν : Set Ω → ℝ≥0∞) : EReal :=
  ⨆ (k : ℕ) (f : Ω → Fin k) (_ : Measurable f),
    klIntegral (R.map f) (Measure.sum fun j ↦ ν (f ⁻¹' {j}) • Measure.dirac j)

variable {ν : Set Ω → ℝ≥0∞}

/-- The definition of `H(R | ν)`, as a supremum over the finite measurable partitions. -/
theorem partitionDivergence_def (R : Measure Ω) (ν : Set Ω → ℝ≥0∞) :
    partitionDivergence R ν = ⨆ (k : ℕ) (f : Ω → Fin k) (_ : Measurable f),
      klIntegral (R.map f) (Measure.sum fun j ↦ ν (f ⁻¹' {j}) • Measure.dirac j) :=
  (rfl)

/-- The divergence on one finite measurable partition is at most `H(R | ν)`. -/
theorem klIntegral_le_partitionDivergence (R : Measure Ω) {k : ℕ} {f : Ω → Fin k}
    (hf : Measurable f) :
    klIntegral (R.map f) (Measure.sum fun j ↦ ν (f ⁻¹' {j}) • Measure.dirac j) ≤
      partitionDivergence R ν :=
  le_iSup₂_of_le (f := fun (k : ℕ) (f : Ω → Fin k) ↦ ⨆ (_ : Measurable f),
    klIntegral (R.map f) (Measure.sum fun j ↦ ν (f ⁻¹' {j}) • Measure.dirac j)) k f
    (le_iSup_of_le hf le_rfl)

/-- The measure on `Fin k` with finite masses `c j` is finite. -/
private lemma isFiniteMeasure_sum_smul_dirac {k : ℕ} (c : Fin k → ℝ≥0∞) (hc : ∀ j, c j ≠ ∞) :
    IsFiniteMeasure (Measure.sum fun j ↦ c j • Measure.dirac j) := by
  refine ⟨?_⟩
  rw [Measure.sum_apply _ .univ]
  simp only [smul_apply, measure_univ, smul_eq_mul, mul_one, tsum_fintype]
  exact ENNReal.sum_lt_top.2 fun j _ ↦ (hc j).lt_top

/-- **Data processing** for the divergence to a set function: for finite measures `R` and `μ`
and a set function `ν` that is finite and at least `μ` on the measurable sets,
`H(R | ν) ≤ klIntegral R μ`. On each partition `f`, the masses of `ν` are at least those of
`μ.map f`, `klIntegral` is antitone in its second argument
(`ProbabilityTheory.klIntegral_anti_right`), and it decreases along `f`
(`ProbabilityTheory.klIntegral_map_le`). In particular `H(R | μ) ≤ klIntegral R μ`. -/
theorem partitionDivergence_le_klIntegral (R : Measure Ω) [IsFiniteMeasure R] {μ : Measure Ω}
    [IsFiniteMeasure μ] (hμν : ∀ s, MeasurableSet s → μ s ≤ ν s)
    (hν : ∀ s, MeasurableSet s → ν s ≠ ∞) :
    partitionDivergence R ν ≤ klIntegral R μ := by
  refine iSup₂_le fun k f ↦ iSup_le fun hf ↦ ?_
  have := isFiniteMeasure_sum_smul_dirac _ fun j ↦ hν _ (hf (measurableSet_singleton j))
  have hle : μ.map f ≤ Measure.sum fun j ↦ ν (f ⁻¹' {j}) • Measure.dirac j := by
    conv_lhs => rw [← Measure.sum_smul_dirac (μ.map f)]
    refine Measure.le_iff.2 fun A hA ↦ ?_
    rw [Measure.sum_apply _ hA, Measure.sum_apply _ hA]
    refine tsum_le_tsum fun j ↦ ?_
    simp only [smul_apply, smul_eq_mul]
    rw [Measure.map_apply hf (measurableSet_singleton j)]
    exact mul_le_mul_left (hμν _ (hf (measurableSet_singleton j))) _
  exact (klIntegral_anti_right hle).trans (klIntegral_map_le hf)

/-! ### The divergence to a finitely additive measure -/

variable {m : AddContent ℝ≥0∞ {s : Set Ω | MeasurableSet s}}

/-- **The bound on a finite partition.** For a finite measure `R`, an additive content `m` of
finite mass on the measurable sets with countably additive part `m_c`, a finite measurable
partition `π`, values `h j` with `|h j| ≤ N` and `η > 0`,
`∑ j, h j R(π = j) - ∑ j, exp (h j) m_c(π = j) + R univ - η ≤ H(R | m)`. The partition is refined
by a set `E` of small `R`-measure that carries all but a small part of `m - m_c`, with the value
`-M` on `E` for a large `M`; the variational lower bound for `klIntegral` on the refined
partition gives the inequality. -/
private lemma sum_sub_sum_exp_add_sub_le_partitionDivergence (R : Measure Ω) [IsFiniteMeasure R]
    (hm : m univ ≠ ∞) {k : ℕ} {π : Ω → Fin k} (hπ : Measurable π) (h : Fin k → ℝ) {N : ℝ}
    (hN : 0 ≤ N) (hhN : ∀ j, |h j| ≤ N) {η : ℝ} (hη : 0 < η) :
    ((∑ j, h j * R.real (π ⁻¹' {j}) -
        ∑ j, Real.exp (h j) * (countablyAdditivePart m).real (π ⁻¹' {j}) + R.real univ - η :
          ℝ) : EReal) ≤ partitionDivergence R m := by
  classical
  set μc := countablyAdditivePart m with hμc
  have : IsFiniteMeasure μc := isFiniteMeasure_countablyAdditivePart hm
  have hmono (A : Set Ω) (hA : MeasurableSet A) : m A ≤ m univ :=
    addContent_mono isSetRing_measurableSet.isSetSemiring hA .univ (subset_univ A)
  have hmfin (A : Set Ω) (hA : MeasurableSet A) : m A ≠ ⊤ := ne_top_of_le_ne_top hm (hmono A hA)
  have hμcm (A : Set Ω) (hA : MeasurableSet A) : μc A ≤ m A := countablyAdditivePart_apply_le m hA
  -- the constants
  set c : ℝ := (m univ).toReal with hc
  have hc0 : 0 ≤ c := ENNReal.toReal_nonneg
  set M : ℝ := max (Real.log (2 * (c + 1) / η)) 0 with hM
  have hM0 : 0 ≤ M := le_max_right _ _
  have hexpM : Real.exp (-M) * c ≤ η / 2 := by
    have h1 : Real.exp (-M) ≤ η / (2 * (c + 1)) := by
      calc Real.exp (-M) ≤ Real.exp (-Real.log (2 * (c + 1) / η)) :=
            Real.exp_le_exp.2 (neg_le_neg (le_max_left _ _))
        _ = η / (2 * (c + 1)) := by rw [Real.exp_neg, Real.exp_log (by positivity), inv_div]
    calc Real.exp (-M) * c ≤ η / (2 * (c + 1)) * c := mul_le_mul_of_nonneg_right h1 hc0
      _ ≤ η / 2 := by
        rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
  set K : ℝ := N + M + Real.exp N + 1 with hK
  have hK0 : 0 < K := by positivity
  set ε : ℝ := η / (2 * K) with hε
  have hε0 : 0 < ε := by positivity
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
  have hcomb : (N + M) * aE + Real.exp N * pE ≤ η / 2 := by
    have h1 : (N + M) * aE + Real.exp N * pE ≤ K * (aE + pE) := by
      have := mul_nonneg (by positivity : (0 : ℝ) ≤ Real.exp N + 1) haE0
      have := mul_nonneg (by positivity : (0 : ℝ) ≤ N + M + 1) hpE0
      nlinarith
    have h2 : K * (aE + pE) ≤ K * ε := mul_le_mul_of_nonneg_left hsmall.le hK0.le
    have h3 : K * ε = η / 2 := by rw [hε]; field_simp
    linarith
  -- the refined partition, with the values `h` off `E` and `-M` on `E`
  set π' : Ω → Fin (k + 1) := fun x ↦ if x ∈ E then Fin.last k else (π x).castSucc with hπ'
  have hπ'm : Measurable π' :=
    Measurable.ite hE measurable_const ((measurable_of_finite Fin.castSucc).comp hπ)
  have hpre (j : Fin k) : π' ⁻¹' {j.castSucc} = π ⁻¹' {j} ∩ Eᶜ := by
    ext x
    by_cases hx : x ∈ E
    · simp [hπ', hx, (Fin.castSucc_lt_last j).ne']
    · simp [hπ', hx]
  have hpreE : π' ⁻¹' {Fin.last k} = E := by
    ext x
    by_cases hx : x ∈ E
    · simp [hπ', hx]
    · simp [hπ', hx, (Fin.castSucc_lt_last _).ne]
  set h' : Fin (k + 1) → ℝ := Fin.snoc h (-M) with hh'
  set ρ := Measure.sum fun i ↦ m (π' ⁻¹' {i}) • Measure.dirac i with hρ
  have : IsFiniteMeasure ρ :=
    isFiniteMeasure_sum_smul_dirac _ fun i ↦ hmfin _ (hπ'm (measurableSet_singleton i))
  -- the variational lower bound on the refined partition
  have hlow := integral_sub_integral_exp_add_le_klIntegral (μ := R.map π') (ν := ρ) (f := h')
    Integrable.of_finite Integrable.of_finite
  have e1 : ∑ i, (R.map π').real {i} • h' i = ∑ i, h' i * R.real (π' ⁻¹' {i}) :=
    Finset.sum_congr rfl fun i _ ↦ by
      rw [smul_eq_mul, mul_comm, map_measureReal_apply hπ'm (measurableSet_singleton i)]
  have e2 : ∑ i, ρ.real {i} • Real.exp (h' i) =
      ∑ i, Real.exp (h' i) * (m (π' ⁻¹' {i})).toReal :=
    Finset.sum_congr rfl fun i _ ↦ by
      rw [smul_eq_mul, mul_comm, measureReal_def, hρ, Measure.sum_smul_dirac_singleton]
  rw [integral_fintype Integrable.of_finite, integral_fintype Integrable.of_finite, e1, e2,
    map_measureReal_apply hπ'm .univ, preimage_univ] at hlow
  refine le_trans ?_ (hlow.trans (klIntegral_le_partitionDivergence R hπ'm))
  rw [EReal.coe_le_coe_iff, Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
  simp only [hh', Fin.snoc_castSucc, Fin.snoc_last, hpre, hpreE]
  -- the facts on the partition
  have hfib (j : Fin k) : MeasurableSet (π ⁻¹' {j}) := hπ (measurableSet_singleton j)
  have hsumC (μ : Measure Ω) [IsFiniteMeasure μ] (C : Set Ω) (hC : MeasurableSet C) :
      ∑ j, μ.real (π ⁻¹' {j} ∩ C) = μ.real C := by
    have := sum_measureReal_preimage_singleton (μ := μ.restrict C) Finset.univ (f := π)
      (fun j _ ↦ hfib j)
    simpa only [Finset.coe_univ, preimage_univ, measureReal_restrict_apply (hfib _),
      measureReal_restrict_apply MeasurableSet.univ, univ_inter] using this
  have hsplit (j : Fin k) :
      R.real (π ⁻¹' {j}) = R.real (π ⁻¹' {j} ∩ Eᶜ) + R.real (π ⁻¹' {j} ∩ E) := by
    rw [add_comm, ← measureReal_inter_add_sdiff (s := π ⁻¹' {j}) hE, Set.sdiff_eq]
  have hmsum : ∑ j, (m (π ⁻¹' {j} ∩ Eᶜ)).toReal = (m Eᶜ).toReal := by
    have hU : ⋃ j ∈ (Finset.univ : Finset (Fin k)), π ⁻¹' {j} ∩ Eᶜ = Eᶜ := by
      ext x
      simp
    have hdisj : ((Finset.univ : Finset (Fin k)) : Set (Fin k)).PairwiseDisjoint
        fun j ↦ π ⁻¹' {j} ∩ Eᶜ := by
      intro i _ j _ hij
      exact ((Set.disjoint_singleton.2 hij).preimage π).mono inter_subset_left inter_subset_left
    have hb := addContent_biUnion_eq (m := m) isSetRing_measurableSet
      (fun j _ ↦ (hfib j).inter hE.compl) hdisj
    rw [hU] at hb
    rw [← ENNReal.toReal_sum (fun j _ ↦ hmfin _ ((hfib j).inter hE.compl)), ← hb]
  have hb1 : ∑ j, h j * R.real (π ⁻¹' {j}) ≤ ∑ j, h j * R.real (π ⁻¹' {j} ∩ Eᶜ) + N * aE := by
    have : ∑ j, h j * R.real (π ⁻¹' {j} ∩ E) ≤ N * aE := by
      calc ∑ j, h j * R.real (π ⁻¹' {j} ∩ E) ≤ ∑ j, N * R.real (π ⁻¹' {j} ∩ E) :=
            Finset.sum_le_sum fun j _ ↦
              mul_le_mul_of_nonneg_right ((le_abs_self _).trans (hhN j)) measureReal_nonneg
        _ = N * aE := by rw [← Finset.mul_sum, hsumC R E hE]
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
      have h1 : μc.real (π ⁻¹' {j} ∩ Eᶜ) ≤ μc.real (π ⁻¹' {j}) :=
        measureReal_mono inter_subset_left
      have h2 : μc.real (π ⁻¹' {j} ∩ Eᶜ) ≤ (m (π ⁻¹' {j} ∩ Eᶜ)).toReal := by
        rw [measureReal_def]
        exact ENNReal.toReal_mono (hmfin _ ((hfib j).inter hE.compl))
          (hμcm _ ((hfib j).inter hE.compl))
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
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib, hmsum,
            hsumC μc Eᶜ hE.compl]
  have hb3 : Real.exp (-M) * (m E).toReal ≤ η / 2 :=
    (mul_le_mul_of_nonneg_left (ENNReal.toReal_mono hm (hmono E hE)) (Real.exp_pos _).le).trans
      hexpM
  nlinarith [hb1, hb2, hb3, hcomb, mul_nonneg hM0 haE0]

/-- **The bound for a bounded measurable function.** For a finite measure `R`, an additive
content `m` of finite mass on the measurable sets with countably additive part `m_c` and a
bounded measurable `g`, `∫ g dR - ∫ exp g dm_c + R univ ≤ H(R | m)`: approximate `g` from below
by a step function. -/
private lemma integral_sub_integral_exp_add_le_partitionDivergence (R : Measure Ω)
    [IsFiniteMeasure R] (hm : m univ ≠ ∞) {g : Ω → ℝ} (hg : Measurable g) {N₀ : ℝ}
    (hgN₀ : ∀ x, |g x| ≤ N₀) :
    ((∫ x, g x ∂R - ∫ x, Real.exp (g x) ∂(countablyAdditivePart m) + R.real univ : ℝ) :
      EReal) ≤ partitionDivergence R m := by
  classical
  set μc := countablyAdditivePart m with hμc
  have : IsFiniteMeasure μc := isFiniteMeasure_countablyAdditivePart hm
  obtain ⟨N, hN, hgN⟩ : ∃ N, 0 ≤ N ∧ ∀ x, |g x| ≤ N :=
    ⟨max N₀ 0, le_max_right _ _, fun x ↦ (hgN₀ x).trans (le_max_left _ _)⟩
  have hRu : 0 ≤ R.real univ := measureReal_nonneg
  have hbdd (μ : Measure Ω) [IsFiniteMeasure μ] {f : Ω → ℝ} (hf : Measurable f) {C : ℝ}
      (hfC : ∀ x, |f x| ≤ C) : Integrable f μ :=
    (integrable_and_integrable_exp hf hfC).1
  have hexpbdd {f : Ω → ℝ} {C : ℝ} (hfC : ∀ x, |f x| ≤ C) (x : Ω) :
      |Real.exp (f x)| ≤ Real.exp C := by
    rw [abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.2 ((le_abs_self _).trans (hfC x))
  have key (η : ℝ) (hη : 0 < η) :
      ((∫ x, g x ∂R - ∫ x, Real.exp (g x) ∂μc + R.real univ - η : ℝ) : EReal) ≤
        partitionDivergence R m := by
    set δ := η / (2 * (R.real univ + 1)) with hδ
    have hδ0 : 0 < δ := div_pos hη (by linarith)
    have hRδ : R.real univ * δ ≤ η / 2 := by
      rw [hδ, ← mul_div_assoc, div_le_div_iff₀ (by linarith) (by norm_num)]
      nlinarith
    -- a step function `g'` below `g`, at distance at most `δ`
    set g' : Ω → ℝ := fun x ↦ δ * ⌊g x / δ⌋ with hg'
    have hgf (x : Ω) : g' x ≤ g x := by
      have h := Int.floor_le (g x / δ)
      calc g' x = δ * ⌊g x / δ⌋ := rfl
        _ ≤ δ * (g x / δ) := by gcongr
        _ = g x := by field_simp
    have hfg (x : Ω) : g x - δ ≤ g' x := by
      have h := Int.lt_floor_add_one (g x / δ)
      have h' : g x / δ - 1 ≤ ⌊g x / δ⌋ := by linarith
      calc g x - δ = δ * (g x / δ - 1) := by field_simp
        _ ≤ δ * ⌊g x / δ⌋ := by gcongr
        _ = g' x := rfl
    have hg'm : Measurable g' := measurable_const.mul
      (measurable_from_top.comp (Int.measurable_floor.comp (hg.div_const δ)))
    have hg'N (x : Ω) : |g' x| ≤ N + δ := by
      rw [abs_le]
      have := abs_le.1 (hgN x)
      exact ⟨by linarith [hfg x], by linarith [hgf x]⟩
    -- the range of `g'` is finite
    have hrange : (Set.range g').Finite := by
      have hsub : Set.range g' ⊆ (fun z : ℤ ↦ δ * z) '' Set.Icc ⌊-N / δ⌋ ⌊N / δ⌋ := by
        rintro _ ⟨x, rfl⟩
        refine ⟨⌊g x / δ⌋, ⟨Int.floor_mono ?_, Int.floor_mono ?_⟩, rfl⟩
        · exact div_le_div_of_nonneg_right (abs_le.1 (hgN x)).1 hδ0.le
        · exact div_le_div_of_nonneg_right (abs_le.1 (hgN x)).2 hδ0.le
      exact ((Set.finite_Icc _ _).image _).subset hsub
    -- `g'` is a function of a finite measurable partition `π`
    have := hrange.fintype
    set e := Fintype.equivFin (Set.range g')
    set π : Ω → Fin (Fintype.card (Set.range g')) := fun x ↦ e ⟨g' x, x, rfl⟩ with hπ
    set h : Fin (Fintype.card (Set.range g')) → ℝ := fun j ↦ (e.symm j : Set.range g') with hh
    have hgπ (x : Ω) : h (π x) = g' x := by simp [hh, hπ]
    have hπm : Measurable π := by
      refine measurable_to_countable' fun i ↦ ?_
      have hi : π ⁻¹' {i} = g' ⁻¹' {((e.symm i : Set.range g') : ℝ)} := by
        ext x
        simp only [Set.mem_preimage, Set.mem_singleton_iff]
        constructor
        · rintro rfl
          exact (hgπ x).symm
        · intro hx
          rw [hπ, ← e.eq_symm_apply]
          exact Subtype.ext hx
      rw [hi]
      exact hg'm (measurableSet_singleton _)
    have hhN (j : Fin (Fintype.card (Set.range g'))) : |h j| ≤ N + δ := by
      obtain ⟨x, hx⟩ := (e.symm j).property
      rw [show h j = g' x from hx.symm]
      exact hg'N x
    -- integrals of functions of `g'` as sums over the cells
    have hint (μ : Measure Ω) [IsFiniteMeasure μ] (φ : ℝ → ℝ) :
        ∫ x, φ (g' x) ∂μ = ∑ j, φ (h j) * μ.real (π ⁻¹' {j}) := by
      calc ∫ x, φ (g' x) ∂μ = ∫ x, φ (h (π x)) ∂μ := by simp_rw [hgπ]
        _ = ∫ j, φ (h j) ∂(μ.map π) := (integral_map hπm.aemeasurable
          (measurable_of_finite (fun j ↦ φ (h j))).aestronglyMeasurable).symm
        _ = ∑ j, (μ.map π).real {j} • φ (h j) := integral_fintype Integrable.of_finite
        _ = ∑ j, φ (h j) * μ.real (π ⁻¹' {j}) := by
          refine Finset.sum_congr rfl fun j _ ↦ ?_
          rw [map_measureReal_apply hπm (measurableSet_singleton j), smul_eq_mul, mul_comm]
    have h1 : ∫ x, g x ∂R ≤ ∑ j, h j * R.real (π ⁻¹' {j}) + R.real univ * δ := by
      have hmono : ∫ x, g x ∂R ≤ ∫ x, (g' x + δ) ∂R := integral_mono (hbdd R hg hgN)
        ((hbdd R hg'm hg'N).add (integrable_const δ)) (fun x ↦ by linarith [hfg x])
      rw [integral_add (hbdd R hg'm hg'N) (integrable_const _), integral_const,
        smul_eq_mul] at hmono
      have hh := hint R id
      simp only [id] at hh
      linarith
    have h2 : ∑ j, Real.exp (h j) * μc.real (π ⁻¹' {j}) ≤ ∫ x, Real.exp (g x) ∂μc := by
      rw [← hint μc Real.exp]
      exact integral_mono (hbdd μc hg'm.exp (hexpbdd hg'N))
        ((integrable_and_integrable_exp hg hgN).2) fun x ↦ Real.exp_le_exp.2 (hgf x)
    have hstep := sum_sub_sum_exp_add_sub_le_partitionDivergence R hm hπm h
      (by positivity : 0 ≤ N + δ) hhN (half_pos hη)
    refine le_trans ?_ hstep
    rw [EReal.coe_le_coe_iff]
    linarith
  -- conclude, letting `η → 0`
  generalize hPD : partitionDivergence R m = PD at key ⊢
  induction PD using EReal.rec with
  | bot => exact absurd (le_bot_iff.1 (key 1 one_pos)) (EReal.coe_ne_bot _)
  | coe r =>
    rw [EReal.coe_le_coe_iff]
    refine le_of_forall_pos_le_add fun η hη ↦ ?_
    have := key η hη
    rw [EReal.coe_le_coe_iff] at this
    linarith
  | top => exact le_top

/-- **The countably additive part carries the divergence** [EVR26, Note 43, Section 3]: for a
finite measure `R` and an additive content `m` of finite mass on the measurable sets,
`klIntegral R m_c ≤ H(R | m)`, with `m_c` the countably additive part of `m`. The variational
formula for `klIntegral` reduces it to bounded measurable functions. -/
theorem klIntegral_countablyAdditivePart_le_partitionDivergence (R : Measure Ω)
    [IsFiniteMeasure R] (hm : m univ ≠ ∞) :
    klIntegral R (countablyAdditivePart m) ≤ partitionDivergence R m := by
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
  refine le_antisymm (partitionDivergence_le_klIntegral R
    (fun s hs ↦ countablyAdditivePart_apply_le m hs) fun s hs ↦ ne_top_of_le_ne_top hm ?_)
    (klIntegral_countablyAdditivePart_le_partitionDivergence R hm)
  exact addContent_mono isSetRing_measurableSet.isSetSemiring hs .univ (subset_univ s)

end ProbabilityTheory
