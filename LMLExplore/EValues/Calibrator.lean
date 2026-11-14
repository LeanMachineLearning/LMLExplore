/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.EValues.PVariable
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Topology.Semicontinuity.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import LMLExplore.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import LMLExplore.Topology.Order.LeftRightLim
import LMLExplore.Topology.Semicontinuity.ENNReal
import Mathlib.Topology.Order.Monotone
import TauCeti.Analysis.SpecialFunctions.Pow.Integral

/-!
# P-to-e calibrators

A p-to-e calibrator is a way of turning p-variables into e-variables: an antitone
`f : ℝ≥0∞ → ℝ≥0∞`, zero on `(1, ∞]`, such that `f ∘ p` is an e-variable for every p-variable `p`
of every null hypothesis of probability measures on every measurable space. By
[RW, Proposition 2.5], these are exactly the antitone functions vanishing on `(1, ∞]` with
`∫₀¹ f ≤ 1`, and this characterization is taken here as the definition. The definition is
justified by `IsPToECalibrator.isEVar_comp` and its converse `isPToECalibrator_iff_isEVar`, whose
proof rests on the fact that a p-variable is stochastically larger than the uniform law on
`[0, 1]` (`IsPVar.lintegral_comp_le`).

A calibrator is admissible when no other calibrator dominates it. The admissible calibrators are
the upper semicontinuous calibrators with `f 0 = ∞` and `∫₀¹ f = 1` [RW, Proposition 2.5].

## Main definitions

* `ProbabilityTheory.IsPToECalibrator f`: `f` is a p-to-e calibrator.
* `ProbabilityTheory.IsAdmissiblePToECalibrator f`: `f` is a calibrator that no other calibrator
  strictly dominates.
* `ProbabilityTheory.powCalibrator κ`: the function `x ↦ κ x ^ (κ - 1)` on `[0, 1]`, zero on
  `(1, ∞]`; it is a calibrator for `0 < κ ≤ 1`.
* `ProbabilityTheory.powMixCalibrator`: the mixture of the calibrators `powCalibrator κ` over
  `κ` uniform on `(0, 1)`.

## Main statements

* `ProbabilityTheory.IsPToECalibrator.isEVar_comp`: for a null of probability measures, a
  calibrator turns every p-variable into an e-variable [VW21, Proposition 2.1], and
  `ProbabilityTheory.isPToECalibrator_iff_isEVar`: an antitone function vanishing on `(1, ∞]` is
  a calibrator as soon as it turns the identity of `[0, 1]`, under Lebesgue measure, into an
  e-variable.
* `ProbabilityTheory.IsPToECalibrator.le_inv`: a calibrator is at most `x ↦ x⁻¹`.
* `ProbabilityTheory.isAdmissiblePToECalibrator_iff`: the characterization of admissible
  calibrators [RW, Proposition 2.5].
* `ProbabilityTheory.IsPToECalibrator.const_mul_comp_mul` and its admissible version: the
  rescaling `x ↦ a f (a x)`, `a ≥ 1`, of a calibrator is a calibrator [RW, Proposition 2.6].
* `ProbabilityTheory.isPToECalibrator_lintegral`: mixtures of calibrators are calibrators.
* `ProbabilityTheory.isAdmissiblePToECalibrator_powCalibrator` and
  `ProbabilityTheory.powMixCalibrator_ofReal`: the power calibrators `powCalibrator κ` are
  admissible for `0 < κ < 1`, and their mixture is `(1 - x + x log x) / (x (log x) ^ 2)` on
  `(0, 1)` [RW, (2.1)–(2.2)].

## References

* A. Ramdas and R. Wang, *Hypothesis Testing with E-values*, Foundations and Trends in
  Statistics 1 (2025), arXiv:2410.23614v6 [RW]: Definition 2.3, Propositions 2.5 and 2.6, (2.1)
  and (2.2).
* V. Vovk and R. Wang, *E-values: calibration, combination and applications*, Ann. Statist. 49
  (2021), arXiv:1912.06116v4 [VW21]: Proposition 2.1.
-/

public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {S : Set (Measure Ω)} {p : Ω → ℝ≥0∞}
  {P : Measure Ω} {f g : ℝ≥0∞ → ℝ≥0∞}

/-! ### Calibrators -/

/-- A **p-to-e calibrator** is an antitone `f : ℝ≥0∞ → ℝ≥0∞`, zero on `(1, ∞]`, with
`∫₀¹ f ≤ 1`. This is the characterization of [RW, Proposition 2.5], taken as the definition:
these are exactly the antitone functions, zero on `(1, ∞]`, that turn every p-variable of every
null of probability measures into an e-variable (`IsPToECalibrator.isEVar_comp`,
`isPToECalibrator_iff_isEVar`). -/
structure IsPToECalibrator (f : ℝ≥0∞ → ℝ≥0∞) : Prop where
  antitone : Antitone f
  eq_zero_of_one_lt : ∀ x, 1 < x → f x = 0
  lintegral_le_one : ∫⁻ x in Icc (0 : ℝ) 1, f (ENNReal.ofReal x) ≤ 1

theorem IsPToECalibrator.measurable (hf : IsPToECalibrator f) : Measurable f :=
  hf.antitone.measurable

/-- **A calibrator turns p-variables into e-variables** [VW21, Proposition 2.1]: for a null of
probability measures, `f ∘ p` is an e-variable for every calibrator `f` and every
p-variable `p`. -/
theorem IsPToECalibrator.isEVar_comp (hf : IsPToECalibrator f)
    (hS : ∀ P ∈ S, IsProbabilityMeasure P) (hp : IsPVar p S) : IsEVar (f ∘ p) S :=
  IsEVar.of_lintegral_le_one hS (hf.measurable.comp hp.measurable) fun P hP ↦
    have := hS P hP
    (hp.lintegral_comp_le hP prob_le_one hf.antitone).trans hf.lintegral_le_one

/-- **The converse**: an antitone function vanishing on `(1, ∞]` is a calibrator exactly when it
turns the identity of `[0, 1]`, an exact p-variable under the Lebesgue measure on `[0, 1]`, into
an e-variable. -/
theorem isPToECalibrator_iff_isEVar :
    IsPToECalibrator f ↔ Antitone f ∧ (∀ x, 1 < x → f x = 0) ∧
      IsEVar (fun x : ℝ ↦ f (ENNReal.ofReal x)) {volume.restrict (Icc 0 1)} := by
  have : IsProbabilityMeasure (volume.restrict (Icc (0 : ℝ) 1)) := ⟨by simp⟩
  refine ⟨fun hf ↦ ⟨hf.antitone, hf.eq_zero_of_one_lt, ?_⟩, fun ⟨h_anti, h_zero, hE⟩ ↦
    ⟨h_anti, h_zero, hE.lintegral_le_one (mem_singleton _)⟩⟩
  exact hf.isEVar_comp (by simp only [mem_singleton_iff, forall_eq]; infer_instance)
    isExactPVar_ofReal_volume.toIsPVar

/-- A calibrator is at most `x ↦ x⁻¹`: `x f x ≤ ∫₀ˣ f ≤ 1`. -/
theorem IsPToECalibrator.le_inv (hf : IsPToECalibrator f) (x : ℝ≥0∞) : f x ≤ x⁻¹ := by
  rcases lt_or_ge 1 x with hx | hx
  · simp [hf.eq_zero_of_one_lt x hx]
  have hx' : x ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top hx
  rw [ENNReal.le_inv_iff_mul_le]
  calc f x * x = ∫⁻ _ in Icc (0 : ℝ) x.toReal, f x := by
        rw [setLIntegral_const, Real.volume_Icc, sub_zero, ENNReal.ofReal_toReal hx']
    _ ≤ ∫⁻ u in Icc (0 : ℝ) x.toReal, f (ENNReal.ofReal u) :=
        setLIntegral_mono (hf.measurable.comp ENNReal.measurable_ofReal) fun u hu ↦
          hf.antitone (ENNReal.ofReal_le_of_le_toReal hu.2)
    _ ≤ ∫⁻ u in Icc (0 : ℝ) 1, f (ENNReal.ofReal u) :=
        lintegral_mono_set (Icc_subset_Icc_right
          (ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using hx)))
    _ ≤ 1 := hf.lintegral_le_one

/-! ### Rescaling and mixtures -/

/-- A function of `ℝ≥0∞` vanishing on `(1, ∞]` has the same integral on `[0, b]`, `b ≥ 1`, as
on `[0, 1]`. -/
private lemma setLIntegral_Icc_ofReal_of_eq_zero (h_zero : ∀ x, 1 < x → f x = 0) {b : ℝ}
    (hb : 1 ≤ b) :
    ∫⁻ x in Icc (0 : ℝ) b, f (ENNReal.ofReal x) = ∫⁻ x in Icc (0 : ℝ) 1, f (ENNReal.ofReal x) := by
  rw [← Icc_union_Ioc_eq_Icc zero_le_one hb, lintegral_union measurableSet_Ioc
    ((Iic_disjoint_Ioc le_rfl).mono_left Icc_subset_Iic_self),
    setLIntegral_congr_fun measurableSet_Ioc (g := 0) fun x hx ↦
      h_zero _ (ENNReal.one_lt_ofReal.2 hx.1)]
  simp

/-- The change of variables behind the rescaling of calibrators. -/
private lemma setLIntegral_const_mul_comp_mul (h_meas : Measurable f)
    (h_zero : ∀ x, 1 < x → f x = 0) {a : ℝ≥0} (ha : 1 ≤ a) :
    ∫⁻ x in Icc (0 : ℝ) 1, (a : ℝ≥0∞) * f (a * ENNReal.ofReal x) =
      ∫⁻ x in Icc (0 : ℝ) 1, f (ENNReal.ofReal x) := by
  have ha0 : (0 : ℝ) < a := zero_lt_one.trans_le (by exact_mod_cast ha)
  have h_cov := TauCeti.setLIntegral_comp_mul_left_mul_rpow (fun t ↦ f (ENNReal.ofReal t)) ha0
    (S := Icc 0 a) (T := Icc 0 1) measurableSet_Icc (fun s ↦ by
      simp only [mem_Icc]
      constructor
      · rintro ⟨h0, h1⟩
        exact ⟨mul_nonneg ha0.le h0, by nlinarith⟩
      · rintro ⟨h0, h1⟩
        exact ⟨nonneg_of_mul_nonneg_right h0 ha0, by nlinarith⟩) Icc_subset_Ici_self 0
  simp only [Real.rpow_zero, ENNReal.ofReal_one, mul_one, zero_add] at h_cov
  have h_eq (x : ℝ) : (a : ℝ≥0∞) * ENNReal.ofReal x = ENNReal.ofReal (a * x) := by
    rw [ENNReal.ofReal_mul ha0.le, ENNReal.ofReal_coe_nnreal]
  simp_rw [h_eq]
  have h_inv : (a : ℝ≥0∞) * ENNReal.ofReal ((a : ℝ) ^ (-1 : ℝ)) = 1 := by
    simp [Real.rpow_neg_one, ENNReal.ofReal_inv_of_pos ha0, ENNReal.mul_inv_cancel,
      (zero_lt_one.trans_le ha).ne']
  rw [lintegral_const_mul (f := fun x ↦ f (ENNReal.ofReal (a * x))) _
      (h_meas.comp (ENNReal.measurable_ofReal.comp (measurable_const_mul _))), h_cov,
    setLIntegral_Icc_ofReal_of_eq_zero h_zero (by exact_mod_cast ha), ← mul_assoc, h_inv, one_mul]

/-- **Rescaling** [RW, Proposition 2.6]: for `a ≥ 1`, `x ↦ a f (a x)` is a calibrator when `f`
is one. -/
theorem IsPToECalibrator.const_mul_comp_mul (hf : IsPToECalibrator f) {a : ℝ≥0} (ha : 1 ≤ a) :
    IsPToECalibrator fun x ↦ a * f (a * x) where
  antitone _ _ hxy := by
    dsimp only
    gcongr
    exact hf.antitone (by gcongr)
  eq_zero_of_one_lt x hx := by
    rw [hf.eq_zero_of_one_lt _ (hx.trans_le (le_mul_of_one_le_left' (by exact_mod_cast ha))),
      mul_zero]
  lintegral_le_one := by
    rw [setLIntegral_const_mul_comp_mul hf.measurable hf.eq_zero_of_one_lt ha]
    exact hf.lintegral_le_one

/-- **Mixtures of calibrators** are calibrators: for a probability measure `π` on the indices and
a measurable family of functions `f i` that are calibrators for `π`-almost every `i`,
`x ↦ ∫⁻ i, f i x ∂π` is a calibrator. -/
theorem isPToECalibrator_lintegral {ι : Type*} [MeasurableSpace ι] {π : Measure ι}
    [IsProbabilityMeasure π] {f : ι → ℝ≥0∞ → ℝ≥0∞} (hf : ∀ᵐ i ∂π, IsPToECalibrator (f i))
    (h_meas : Measurable (Function.uncurry f)) :
    IsPToECalibrator fun x ↦ ∫⁻ i, f i x ∂π where
  antitone _ _ hxy := lintegral_mono_ae (hf.mono fun _ hi ↦ hi.antitone hxy)
  eq_zero_of_one_lt x hx := by
    rw [lintegral_congr_ae (g := 0) (hf.mono fun _ hi ↦ hi.eq_zero_of_one_lt x hx)]
    simp
  lintegral_le_one := by
    rw [lintegral_lintegral_swap (f := fun x i ↦ f i (ENNReal.ofReal x))
      (h_meas.comp (measurable_snd.prodMk
        (ENNReal.measurable_ofReal.comp measurable_fst))).aemeasurable]
    calc ∫⁻ i, (∫⁻ x in Icc (0 : ℝ) 1, f i (ENNReal.ofReal x)) ∂π ≤ ∫⁻ _, 1 ∂π :=
          lintegral_mono_ae (hf.mono fun _ hi ↦ hi.lintegral_le_one)
      _ = 1 := by simp

/-! ### Admissible calibrators -/

/-- A calibrator is **admissible** when no other calibrator strictly dominates it: every
calibrator `g ≥ f` is `f` [RW, Definition 2.3]. They are characterized in
`isAdmissiblePToECalibrator_iff`. -/
structure IsAdmissiblePToECalibrator (f : ℝ≥0∞ → ℝ≥0∞) : Prop extends IsPToECalibrator f where
  eq_of_le : ∀ g, IsPToECalibrator g → f ≤ g → g = f

/-- Adding the constant `1 - ∫₀¹ f` on `[0, 1]` to a calibrator gives a calibrator of integral
`1`. -/
private lemma IsPToECalibrator.add_indicator (hf : IsPToECalibrator f) :
    IsPToECalibrator (fun x ↦ f x +
        (Iic 1).indicator (fun _ ↦ 1 - ∫⁻ u in Icc (0 : ℝ) 1, f (ENNReal.ofReal u)) x) ∧
      ∫⁻ x in Icc (0 : ℝ) 1, (f (ENNReal.ofReal x) +
        (Iic 1).indicator (fun _ ↦ 1 - ∫⁻ u in Icc (0 : ℝ) 1, f (ENNReal.ofReal u))
          (ENNReal.ofReal x)) = 1 := by
  set c := 1 - ∫⁻ u in Icc (0 : ℝ) 1, f (ENNReal.ofReal u)
  have h_int : ∫⁻ x in Icc (0 : ℝ) 1, (f (ENNReal.ofReal x) +
      (Iic 1).indicator (fun _ ↦ c) (ENNReal.ofReal x)) = 1 := by
    rw [lintegral_add_left (f := fun x ↦ f (ENNReal.ofReal x))
        (hf.measurable.comp ENNReal.measurable_ofReal),
      setLIntegral_congr_fun measurableSet_Icc
        (f := fun x ↦ (Iic 1).indicator (fun _ ↦ c) (ENNReal.ofReal x)) (g := fun _ ↦ c)
        fun x hx ↦ indicator_of_mem (ENNReal.ofReal_le_one.2 hx.2) _]
    simp [c, add_tsub_cancel_of_le hf.lintegral_le_one]
  refine ⟨⟨fun x y hxy ↦ add_le_add (hf.antitone hxy) ?_, fun x hx ↦ ?_, h_int.le⟩, h_int⟩
  · by_cases hy : y ≤ 1
    · simp [indicator_of_mem (mem_Iic.2 hy),
        indicator_of_mem (mem_Iic.2 (hxy.trans hy))]
    · simp [indicator_of_notMem (mt mem_Iic.1 hy)]
  · simp [hf.eq_zero_of_one_lt x hx, indicator_of_notMem (mt mem_Iic.1 (not_le.2 hx))]

/-- Setting a calibrator to `∞` at `0` gives a calibrator. -/
private lemma IsPToECalibrator.ite_zero (hf : IsPToECalibrator f) :
    IsPToECalibrator fun x ↦ if x = 0 then ∞ else f x where
  antitone x y hxy := by
    by_cases hx : x = 0
    · simp [hx]
    · simp [hx, ((pos_iff_ne_zero.2 hx).trans_le hxy).ne', hf.antitone hxy]
  eq_zero_of_one_lt x hx := by simp [(zero_le_one.trans_lt hx).ne', hf.eq_zero_of_one_lt x hx]
  lintegral_le_one := by
    rw [← setLIntegral_congr Ioc_ae_eq_Icc, setLIntegral_congr_fun measurableSet_Ioc
      (g := fun x ↦ f (ENNReal.ofReal x)) fun x hx ↦ by simp [hx.1],
      setLIntegral_congr Ioc_ae_eq_Icc]
    exact hf.lintegral_le_one

/-- The left limit `Function.leftLim f` of a calibrator, its upper semicontinuous
regularization, is a calibrator. -/
private lemma IsPToECalibrator.leftLim (hf : IsPToECalibrator f) :
    IsPToECalibrator (Function.leftLim f) where
  antitone := hf.antitone.leftLim
  eq_zero_of_one_lt x hx := by
    obtain ⟨y, h1y, hyx⟩ := exists_between hx
    exact nonpos_iff_eq_zero.1
      ((hf.antitone.leftLim_le hyx).trans_eq (hf.eq_zero_of_one_lt y h1y))
  lintegral_le_one := by
    refine le_of_eq_of_le (lintegral_congr_ae ?_) hf.lintegral_le_one
    -- the left limit differs from `f` only at its countably many discontinuities
    have h_null : volume (ENNReal.toReal '' {x | ¬ContinuousAt f x}) = 0 :=
      (hf.antitone.countable_not_continuousAt.image _).measure_zero _
    filter_upwards [ae_restrict_mem measurableSet_Icc,
      ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.1 h_null)] with u hu hu_null
    refine ContinuousWithinAt.leftLim_eq (ContinuousAt.continuousWithinAt ?_)
    by_contra h
    exact hu_null ⟨_, h, ENNReal.toReal_ofReal hu.1⟩

/-- An upper semicontinuous function with `f 0 = ∞` and `∫₀¹ f = 1` is dominated by no calibrator
other than itself. -/
private lemma eq_of_le_of_upperSemicontinuous
    (h_usc : UpperSemicontinuous f) (h_top : f 0 = ∞)
    (h_int : ∫⁻ x in Icc (0 : ℝ) 1, f (ENNReal.ofReal x) = 1) (hg : IsPToECalibrator g)
    (hfg : f ≤ g) : g = f := by
  -- `g` and `f` have the same integral, so they agree almost everywhere on `[0, 1]`
  have h_ae : ∀ᵐ u ∂volume.restrict (Icc (0 : ℝ) 1),
      f (ENNReal.ofReal u) = g (ENNReal.ofReal u) :=
    ae_eq_of_ae_le_of_lintegral_le (.of_forall fun _ ↦ hfg _) (by simp [h_int])
      (hg.measurable.comp ENNReal.measurable_ofReal).aemeasurable
      (hg.lintegral_le_one.trans_eq h_int.symm)
  refine funext fun x ↦ le_antisymm ?_ (hfg x)
  rcases eq_or_ne x 0 with rfl | hx0
  · simp [h_top]
  rcases lt_or_ge 1 x with hx1 | hx1
  · simp [hg.eq_zero_of_one_lt x hx1]
  by_contra h_lt
  rw [not_le] at h_lt
  -- by upper semicontinuity, `f < g x ≤ g` on an interval to the left of `x`
  obtain ⟨l, u, ⟨hlx, hxu⟩, h_sub⟩ := (mem_nhds_iff_exists_Ioo_subset'
    ⟨0, pos_iff_ne_zero.2 hx0⟩ ⟨2, hx1.trans_lt ENNReal.one_lt_two⟩).1 (h_usc x _ h_lt)
  have hx_top : x ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top hx1
  have hl_top : l ≠ ∞ := (hlx.trans_le le_top).ne
  have h_pos : 0 < volume.restrict (Icc (0 : ℝ) 1) (Ioo l.toReal x.toReal) := by
    rw [Measure.restrict_apply measurableSet_Ioo,
      inter_eq_left.2 fun v (hv : v ∈ Ioo l.toReal x.toReal) ↦ mem_Icc.2
        ⟨ENNReal.toReal_nonneg.trans hv.1.le, hv.2.le.trans
          (ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using hx1))⟩, Real.volume_Ioo]
    exact ENNReal.ofReal_pos.2 (sub_pos.2 ((ENNReal.toReal_lt_toReal hl_top hx_top).2 hlx))
  refine h_pos.ne' (measure_mono_null (fun v hv ↦ ?_) (ae_iff.1 h_ae))
  have hv0 : 0 ≤ v := ENNReal.toReal_nonneg.trans hv.1.le
  have hv_mem : ENNReal.ofReal v ∈ Ioo l u :=
    ⟨(ENNReal.lt_ofReal_iff_toReal_lt hl_top).2 hv.1,
      ((ENNReal.ofReal_lt_iff_lt_toReal hv0 hx_top).2 hv.2).trans hxu⟩
  exact (h_sub hv_mem).trans_le (hg.antitone ((ENNReal.ofReal_lt_iff_lt_toReal hv0 hx_top).2
    hv.2).le) |>.ne

/-- **Admissible calibrators** [RW, Proposition 2.5]: a calibrator is admissible exactly when it
is upper semicontinuous, `f 0 = ∞` and `∫₀¹ f = 1`. -/
theorem isAdmissiblePToECalibrator_iff :
    IsAdmissiblePToECalibrator f ↔ IsPToECalibrator f ∧ UpperSemicontinuous f ∧ f 0 = ∞ ∧
      ∫⁻ x in Icc (0 : ℝ) 1, f (ENNReal.ofReal x) = 1 := by
  refine ⟨fun hf ↦ ⟨hf.toIsPToECalibrator, ?_, ?_, ?_⟩, fun ⟨hf, h_usc, h_top, h_int⟩ ↦
    ⟨hf, fun g hg hfg ↦ eq_of_le_of_upperSemicontinuous h_usc h_top h_int hg hfg⟩⟩
  · rw [← hf.eq_of_le _ hf.leftLim fun x ↦ hf.antitone.le_leftLim le_rfl]
    exact hf.antitone.upperSemicontinuous_leftLim
  · rw [← hf.eq_of_le _ hf.ite_zero fun x ↦ by by_cases hx : x = 0 <;> simp [hx]]
    simp
  · have h := hf.toIsPToECalibrator.add_indicator
    have h_eq := hf.eq_of_le _ h.1 fun x ↦ le_self_add
    refine Eq.trans ?_ h.2
    exact setLIntegral_congr_fun measurableSet_Icc fun x _ ↦
      (congrFun h_eq (ENNReal.ofReal x)).symm

/-- **Rescaling** of admissible calibrators [RW, Proposition 2.6]: for `a ≥ 1`, `x ↦ a f (a x)`
is admissible when `f` is. -/
theorem IsAdmissiblePToECalibrator.const_mul_comp_mul (hf : IsAdmissiblePToECalibrator f)
    {a : ℝ≥0} (ha : 1 ≤ a) : IsAdmissiblePToECalibrator fun x ↦ a * f (a * x) := by
  obtain ⟨hf, h_usc, h_top, h_int⟩ := isAdmissiblePToECalibrator_iff.1 hf
  have ha0 : (a : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (zero_lt_one.trans_le ha).ne'
  refine isAdmissiblePToECalibrator_iff.2 ⟨hf.const_mul_comp_mul ha, ?_, by simp [h_top, ha0], ?_⟩
  · exact (h_usc.comp (ENNReal.continuous_const_mul ENNReal.coe_ne_top)).ennreal_const_mul
      ENNReal.coe_ne_top
  · rw [setLIntegral_const_mul_comp_mul hf.measurable hf.eq_zero_of_one_lt ha, h_int]

/-! ### Power calibrators -/

/-- The **power calibrator** `x ↦ κ x ^ (κ - 1)` on `[0, 1]`, zero on `(1, ∞]` [RW, (2.1)]. It is
defined for every real `κ` and is a calibrator for `0 < κ ≤ 1` (`isPToECalibrator_powCalibrator`);
for `κ ≤ 0` it is identically `0`, since `ENNReal.ofReal κ = 0`. For `0 < κ < 1` its value at `0`
is `κ 0 ^ (κ - 1) = ∞`. -/
noncomputable def powCalibrator (κ : ℝ) (x : ℝ≥0∞) : ℝ≥0∞ :=
  if x ≤ 1 then ENNReal.ofReal κ * x ^ (κ - 1) else 0

theorem powCalibrator_def (κ : ℝ) (x : ℝ≥0∞) :
    powCalibrator κ x = if x ≤ 1 then ENNReal.ofReal κ * x ^ (κ - 1) else 0 :=
  (rfl)

@[simp]
theorem powCalibrator_of_le_one (κ : ℝ) {x : ℝ≥0∞} (hx : x ≤ 1) :
    powCalibrator κ x = ENNReal.ofReal κ * x ^ (κ - 1) := by
  simp [powCalibrator_def, hx]

@[simp]
theorem powCalibrator_of_one_lt (κ : ℝ) {x : ℝ≥0∞} (hx : 1 < x) : powCalibrator κ x = 0 := by
  simp [powCalibrator_def, not_le.2 hx]

theorem measurable_uncurry_powCalibrator : Measurable (Function.uncurry powCalibrator) := by
  simp only [Function.uncurry_def, powCalibrator_def]
  refine Measurable.ite (measurableSet_le measurable_snd measurable_const) ?_ measurable_const
  exact (ENNReal.measurable_ofReal.comp measurable_fst).mul
    (measurable_snd.pow (measurable_fst.sub_const 1))

/-- The integral of `powCalibrator κ` on `[0, 1]` is `1` for `κ > 0`. -/
theorem setLIntegral_powCalibrator {κ : ℝ} (hκ : 0 < κ) :
    ∫⁻ x in Icc (0 : ℝ) 1, powCalibrator κ (ENNReal.ofReal x) = 1 := by
  rw [← setLIntegral_congr Ioo_ae_eq_Icc, setLIntegral_congr_fun measurableSet_Ioo
    (g := fun x ↦ ENNReal.ofReal κ * ENNReal.ofReal (x ^ (κ - 1))) fun x hx ↦ by
      rw [powCalibrator_of_le_one _ (ENNReal.ofReal_le_one.2 hx.2.le),
        ENNReal.ofReal_rpow_of_pos hx.1],
    lintegral_const_mul _ (by fun_prop),
    TauCeti.lintegral_ofReal_rpow_Ioo (by linarith) zero_le_one, ← ENNReal.ofReal_mul hκ.le]
  simp [hκ.ne']

/-- The power calibrators `x ↦ κ x ^ (κ - 1)`, `0 < κ ≤ 1`, are calibrators. -/
theorem isPToECalibrator_powCalibrator {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) :
    IsPToECalibrator (powCalibrator κ) where
  antitone x y hxy := by
    rcases le_or_gt y 1 with hy | hy
    · rw [powCalibrator_of_le_one _ hy, powCalibrator_of_le_one _ (hxy.trans hy),
        ← neg_sub, ENNReal.rpow_neg, ENNReal.rpow_neg]
      gcongr
    · simp [hy]
  eq_zero_of_one_lt _ hx := powCalibrator_of_one_lt _ hx
  lintegral_le_one := (setLIntegral_powCalibrator hκ0).le

/-- The power calibrator `powCalibrator κ` is upper semicontinuous, for every real `κ`. -/
theorem upperSemicontinuous_powCalibrator (κ : ℝ) : UpperSemicontinuous (powCalibrator κ) := by
  -- below `1`, `powCalibrator κ` is dominated by a continuous function that it equals there
  intro x
  have h_cont : Continuous fun y : ℝ≥0∞ ↦ ENNReal.ofReal κ * y ^ (κ - 1) :=
    (ENNReal.continuous_const_mul ENNReal.ofReal_ne_top).comp ENNReal.continuous_rpow_const
  rcases le_or_gt x 1 with hx | hx
  · intro c hc
    rw [powCalibrator_of_le_one _ hx] at hc
    filter_upwards [h_cont.continuousAt.eventually (gt_mem_nhds hc)] with y hy
    rcases le_or_gt y 1 with hy1 | hy1
    · rwa [powCalibrator_of_le_one _ hy1]
    · rw [powCalibrator_of_one_lt _ hy1]
      exact zero_le.trans_lt hy
  · intro c hc
    rw [powCalibrator_of_one_lt _ hx] at hc
    filter_upwards [Ioi_mem_nhds hx] with y hy
    rwa [powCalibrator_of_one_lt _ hy]

/-- The power calibrators `x ↦ κ x ^ (κ - 1)`, `0 < κ < 1`, are admissible [RW, (2.1)]. -/
theorem isAdmissiblePToECalibrator_powCalibrator {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ < 1) :
    IsAdmissiblePToECalibrator (powCalibrator κ) := by
  refine isAdmissiblePToECalibrator_iff.2 ⟨isPToECalibrator_powCalibrator hκ0 hκ1.le,
    upperSemicontinuous_powCalibrator κ, ?_, setLIntegral_powCalibrator hκ0⟩
  rw [powCalibrator_of_le_one _ zero_le_one, ENNReal.zero_rpow_of_neg (by linarith),
    ENNReal.mul_top (by simpa using hκ0)]

/-! ### The mixture of the power calibrators -/

/-- The mixture `x ↦ ∫₀¹ κ x ^ (κ - 1) dκ` of the power calibrators over `κ` uniform on `(0, 1)`
[RW, (2.2)]; it is `(1 - x + x log x) / (x (log x) ^ 2)` on `(0, 1)`
(`powMixCalibrator_ofReal`). -/
noncomputable def powMixCalibrator (x : ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻ κ in Ioo (0 : ℝ) 1, powCalibrator κ x

theorem powMixCalibrator_def (x : ℝ≥0∞) :
    powMixCalibrator x = ∫⁻ κ in Ioo (0 : ℝ) 1, powCalibrator κ x :=
  (rfl)

/-- The mixture of the power calibrators is a calibrator. -/
theorem isPToECalibrator_powMixCalibrator : IsPToECalibrator powMixCalibrator := by
  have : IsProbabilityMeasure (volume.restrict (Ioo (0 : ℝ) 1)) := ⟨by simp⟩
  simp_rw [funext powMixCalibrator_def]
  refine isPToECalibrator_lintegral ?_ measurable_uncurry_powCalibrator
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with κ hκ
  exact isPToECalibrator_powCalibrator hκ.1 hκ.2.le

/-- **The closed form of the mixture of the power calibrators** [RW, (2.2)]: on `(0, 1)`,
`∫₀¹ κ x ^ (κ - 1) dκ = (1 - x + x log x) / (x (log x) ^ 2)`. -/
theorem powMixCalibrator_ofReal {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    powMixCalibrator (ENNReal.ofReal x) =
      ENNReal.ofReal ((1 - x + x * Real.log x) / (x * Real.log x ^ 2)) := by
  have hlog : Real.log x ≠ 0 := (Real.log_neg hx0 hx1).ne
  have h_cont : Continuous fun κ : ℝ ↦ κ * x ^ (κ - 1) :=
    continuous_id.mul ((Real.continuous_const_rpow hx0.ne').comp (continuous_sub_right 1))
  have h_int : ∫ κ in (0 : ℝ)..1, κ * x ^ (κ - 1) =
      (1 - x + x * Real.log x) / (x * Real.log x ^ 2) := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun κ _ ↦ Real.hasDerivAt_const_rpow_sub_one_mul_div hx0 hlog κ)
      (h_cont.intervalIntegrable _ _)]
    simp only [sub_self, Real.rpow_zero, one_mul, zero_sub, zero_mul, Real.rpow_neg_one]
    field_simp
    ring
  rw [powMixCalibrator_def, ← h_int, intervalIntegral.integral_of_le zero_le_one,
    ofReal_integral_eq_lintegral_ofReal (h_cont.integrableOn_Icc.mono_set Ioc_subset_Icc_self)
      (ae_restrict_of_forall_mem measurableSet_Ioc fun κ hκ ↦
        mul_nonneg hκ.1.le (Real.rpow_nonneg hx0.le _)), ← setLIntegral_congr Ioo_ae_eq_Ioc]
  refine setLIntegral_congr_fun measurableSet_Ioo fun κ hκ ↦ ?_
  rw [powCalibrator_of_le_one _ (ENNReal.ofReal_le_one.2 hx1.le), ENNReal.ofReal_rpow_of_pos hx0,
    ← ENNReal.ofReal_mul hκ.1.le]

end ProbabilityTheory
