/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Function.ConditionalLExpectation
public import Statlib.EValues.EVariable

/-!
# Conditional e-variables

A conditional e-variable given a σ-algebra `m` for a set of measures `S` is a measurable
`X : Ω → ℝ≥0∞` whose conditional expectation given `m` is at most `1` under every `P ∈ S`. It is
stated with set integrals, `∫⁻ ω in s, X ω ∂P ≤ P s` for every `m`-measurable `s`, which needs
neither integrability nor σ-finiteness of the restriction of `P` to `m`. When those restrictions
are σ-finite, it is the bound `P⁻[X|m] ≤ 1` on Mathlib's conditional expectation
`MeasureTheory.condLExp` of `ℝ≥0∞`-valued variables. Conditional
e-variables are the factors of test supermartingales: the factor of round `n` of a product of
sequential e-variables, of a bet or of a portfolio is a conditional e-variable given the past
`ℱ n` [GdHK24, Definition 1; RW, Proposition 7.20].

A known factor can be pulled out: `∫⁻ Y * X ∂P ≤ ∫⁻ Y ∂P` for every `m`-measurable `Y`, through
`MeasureTheory.lintegral_mul_le_lintegral_mul_of_forall_setLIntegral_le`. Hence a portfolio
`∑ i, w i * E i` of conditional e-variables with `m`-measurable weights summing to at most `1` is
a conditional e-variable.

## Main definitions

* `ProbabilityTheory.IsCondEVar X m S`: `X` is a conditional e-variable given `m` for `S`.
* `ProbabilityTheory.IsExactCondEVar X m S`: `X` is an exact conditional e-variable,
  `∫⁻ ω in s, X ω ∂P = P s` for every `m`-measurable `s`.

## Main statements

* `ProbabilityTheory.isCondEVar_iff_withDensity_trim_le`: `X` is a conditional e-variable exactly
  when the restriction of `P.withDensity X` to `m` is at most that of `P`.
* `ProbabilityTheory.isCondEVar_iff_condLExp_le`,
  `ProbabilityTheory.isExactCondEVar_iff_condLExp_eq`: for σ-finite restrictions to `m`, the
  bounds `P⁻[X|m] ≤ 1` and `P⁻[X|m] = 1` on the conditional expectation.
* `ProbabilityTheory.isCondEVar_bot_iff`: for a null of finite measures, the conditional
  e-variables given `⊥` are Statlib's e-variables.
* `ProbabilityTheory.IsCondEVar.setLIntegral_mul_le`: an `m`-measurable factor can be pulled out.
* `ProbabilityTheory.isCondEVar_sum_mul`, `ProbabilityTheory.isExactCondEVar_sum_mul`:
  portfolios of conditional e-variables.

## References

* [RW] A. Ramdas and R. Wang, *Hypothesis Testing with E-values*, Foundations and Trends in
  Statistics 1 (2025), arXiv:2410.23614.
* [GdHK24] P. Grünwald, R. de Heide and W. M. Koolen, *Safe testing*, J. R. Stat. Soc. Ser. B 86
  (2024), arXiv:1906.07801.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace ProbabilityTheory

variable {Ω ι : Type*} {m m' mΩ : MeasurableSpace Ω} {S T : Set (Measure Ω)} {P : Measure Ω}
  {X Y : Ω → ℝ≥0∞} {s : Set Ω}

/-- `X` is a conditional e-variable given the σ-algebra `m` for the set of measures `S`: it is
measurable, and its conditional expectation given `m` is at most `1` under every `P ∈ S`, in the
form `∫⁻ ω in s, X ω ∂P ≤ P s` for every `m`-measurable `s`. -/
structure IsCondEVar (X : Ω → ℝ≥0∞) (m : MeasurableSpace Ω) (S : Set (@Measure Ω mΩ)) :
    Prop where
  measurable : Measurable[mΩ] X
  setLIntegral_le : ∀ P ∈ S, ∀ s, MeasurableSet[m] s → ∫⁻ ω in s, X ω ∂P ≤ P s

/-- `X` is an exact conditional e-variable given the σ-algebra `m` for the set of measures `S`: it
is measurable, and its conditional expectation given `m` is `1` under every `P ∈ S`, in the form
`∫⁻ ω in s, X ω ∂P = P s` for every `m`-measurable `s`. -/
structure IsExactCondEVar (X : Ω → ℝ≥0∞) (m : MeasurableSpace Ω) (S : Set (@Measure Ω mΩ)) :
    Prop where
  measurable : Measurable[mΩ] X
  setLIntegral_eq : ∀ P ∈ S, ∀ s, MeasurableSet[m] s → ∫⁻ ω in s, X ω ∂P = P s

/-- An exact conditional e-variable is a conditional e-variable. -/
theorem IsExactCondEVar.isCondEVar (hX : IsExactCondEVar X m S) : IsCondEVar X m S :=
  ⟨hX.measurable, fun P hP s hs ↦ (hX.setLIntegral_eq P hP s hs).le⟩

/-- The constant `1` is an exact conditional e-variable given every σ-algebra. -/
@[simp]
theorem isExactCondEVar_one : IsExactCondEVar 1 m S :=
  ⟨measurable_const, fun _ _ _ _ ↦ by simp⟩

/-- The constant `1` is a conditional e-variable given every σ-algebra. -/
@[simp]
theorem isCondEVar_one : IsCondEVar 1 m S :=
  isExactCondEVar_one.isCondEVar

/-! ### Monotonicity and congruence -/

namespace IsCondEVar

/-- A conditional e-variable for `T` is one for every subset of `T`. -/
theorem anti_set (hST : S ⊆ T) (hX : IsCondEVar X m T) : IsCondEVar X m S :=
  ⟨hX.measurable, fun P hP ↦ hX.setLIntegral_le P (hST hP)⟩

/-- A conditional e-variable given `m` is one given every coarser σ-algebra. -/
theorem of_le (hm : m' ≤ m) (hX : IsCondEVar X m S) : IsCondEVar X m' S :=
  ⟨hX.measurable, fun P hP s hs ↦ hX.setLIntegral_le P hP s (hm s hs)⟩

/-- A measurable function almost surely equal to a conditional e-variable under every member of
the null is a conditional e-variable. -/
theorem congr (hX : IsCondEVar X m S) (hY : Measurable Y) (hXY : ∀ P ∈ S, X =ᵐ[P] Y) :
    IsCondEVar Y m S :=
  ⟨hY, fun P hP s hs ↦
    (lintegral_congr_ae (ae_restrict_of_ae (hXY P hP))).symm.trans_le
      (hX.setLIntegral_le P hP s hs)⟩

end IsCondEVar

namespace IsExactCondEVar

/-- An exact conditional e-variable for `T` is one for every subset of `T`. -/
theorem anti_set (hST : S ⊆ T) (hX : IsExactCondEVar X m T) : IsExactCondEVar X m S :=
  ⟨hX.measurable, fun P hP ↦ hX.setLIntegral_eq P (hST hP)⟩

/-- An exact conditional e-variable given `m` is one given every coarser σ-algebra. -/
theorem of_le (hm : m' ≤ m) (hX : IsExactCondEVar X m S) : IsExactCondEVar X m' S :=
  ⟨hX.measurable, fun P hP s hs ↦ hX.setLIntegral_eq P hP s (hm s hs)⟩

/-- A measurable function almost surely equal to an exact conditional e-variable under every
member of the null is an exact conditional e-variable. -/
theorem congr (hX : IsExactCondEVar X m S) (hY : Measurable Y) (hXY : ∀ P ∈ S, X =ᵐ[P] Y) :
    IsExactCondEVar Y m S :=
  ⟨hY, fun P hP s hs ↦
    (lintegral_congr_ae (ae_restrict_of_ae (hXY P hP))).symm.trans
      (hX.setLIntegral_eq P hP s hs)⟩

end IsExactCondEVar

/-! ### Characterizations -/

/-- `X` is a conditional e-variable given a sub-σ-algebra `m` exactly when it is measurable and,
for every `P ∈ S`, the restriction of `P.withDensity X` to `m` is at most that of `P`. -/
theorem isCondEVar_iff_withDensity_trim_le (hm : m ≤ mΩ) :
    IsCondEVar X m S ↔ Measurable X ∧ ∀ P ∈ S, (P.withDensity X).trim hm ≤ P.trim hm := by
  have h (P : Measure Ω) : (P.withDensity X).trim hm ≤ P.trim hm ↔
      ∀ s, MeasurableSet[m] s → ∫⁻ ω in s, X ω ∂P ≤ P s := by
    simpa using withDensity_trim_le_withDensity_trim_iff (μ := P) (f := X) (g := 1) hm
  simp_rw [h]
  exact ⟨fun hX ↦ ⟨hX.measurable, hX.setLIntegral_le⟩, fun hX ↦ ⟨hX.1, hX.2⟩⟩

/-- `X` is an exact conditional e-variable given a sub-σ-algebra `m` exactly when it is
measurable and, for every `P ∈ S`, the restrictions of `P.withDensity X` and of `P` to `m` are
equal. -/
theorem isExactCondEVar_iff_withDensity_trim_eq (hm : m ≤ mΩ) :
    IsExactCondEVar X m S ↔ Measurable X ∧ ∀ P ∈ S, (P.withDensity X).trim hm = P.trim hm := by
  have h (P : Measure Ω) : (P.withDensity X).trim hm = P.trim hm ↔
      ∀ s, MeasurableSet[m] s → ∫⁻ ω in s, X ω ∂P = P s := by
    simpa using withDensity_trim_eq_withDensity_trim_iff (μ := P) (f := X) (g := 1) hm
  simp_rw [h]
  exact ⟨fun hX ↦ ⟨hX.measurable, hX.setLIntegral_eq⟩, fun hX ↦ ⟨hX.1, hX.2⟩⟩

/-- When the restrictions to a sub-σ-algebra `m` of the members of `S` are σ-finite, `X` is a
conditional e-variable given `m` exactly when it is measurable and its conditional expectation
`P⁻[X|m]` is almost surely at most `1` under every `P ∈ S`. -/
theorem isCondEVar_iff_condLExp_le (hm : m ≤ mΩ) (hS : ∀ P ∈ S, SigmaFinite (P.trim hm)) :
    IsCondEVar X m S ↔ Measurable X ∧ ∀ P ∈ S, P⁻[X|m] ≤ᵐ[P] 1 := by
  refine ⟨fun hX ↦ ⟨hX.measurable, fun P hP ↦ ?_⟩, fun hX ↦ ⟨hX.1, fun P hP s hs ↦ ?_⟩⟩ <;>
    have := hS P hP
  · refine ae_le_of_ae_le_trim (hm := hm) <| ae_le_of_forall_setLIntegral_le_of_sigmaFinite
      (μ := P.trim hm) (measurable_condLExp _ _ _) fun s hs _ ↦ ?_
    rw [setLIntegral_condLExp_trim hm _ _ hs]
    simpa [trim_measurableSet_eq hm hs] using hX.setLIntegral_le P hP s hs
  · rw [← setLIntegral_condLExp hm P X hs]
    simpa using lintegral_mono_ae (ae_restrict_of_ae (hX.2 P hP))

/-- When the restrictions to a sub-σ-algebra `m` of the members of `S` are σ-finite, `X` is an
exact conditional e-variable given `m` exactly when it is measurable and its conditional
expectation `P⁻[X|m]` is almost surely `1` under every `P ∈ S`. -/
theorem isExactCondEVar_iff_condLExp_eq (hm : m ≤ mΩ) (hS : ∀ P ∈ S, SigmaFinite (P.trim hm)) :
    IsExactCondEVar X m S ↔ Measurable X ∧ ∀ P ∈ S, P⁻[X|m] =ᵐ[P] 1 := by
  refine ⟨fun hX ↦ ⟨hX.measurable, fun P hP ↦ ?_⟩, fun hX ↦ ⟨hX.1, fun P hP s hs ↦ ?_⟩⟩ <;>
    have := hS P hP
  · exact (ae_eq_condLExp hm P X (Y := 1) (by fun_prop) fun s hs ↦ by
      simpa using (hX.setLIntegral_eq P hP s hs).symm).symm
  · rw [← setLIntegral_condLExp hm P X hs, lintegral_congr_ae (ae_restrict_of_ae (hX.2 P hP))]
    simp

/-- For a null of finite measures, the conditional e-variables given the trivial σ-algebra are
exactly the e-variables. -/
theorem isCondEVar_bot_iff (hS : ∀ P ∈ S, IsFiniteMeasure P) :
    IsCondEVar X ⊥ S ↔ IsEVar X S := by
  refine ⟨fun hX ↦ IsEVar.of_lintegral_le_measure_univ hS hX.measurable fun P hP ↦ ?_,
    fun hX ↦ ⟨hX.measurable, fun P hP s hs ↦ ?_⟩⟩
  · simpa using hX.setLIntegral_le P hP univ MeasurableSet.univ
  · rcases MeasurableSpace.measurableSet_bot_iff.1 hs with rfl | rfl
    · simp
    · simpa using hX.lintegral_le_measure_univ P hP

/-- A conditional e-variable given any σ-algebra is an e-variable for a null of finite
measures. -/
theorem IsCondEVar.isEVar (hS : ∀ P ∈ S, IsFiniteMeasure P) (hX : IsCondEVar X m S) :
    IsEVar X S :=
  (isCondEVar_bot_iff hS).1 (hX.of_le bot_le)

/-! ### Pulling out a known factor -/

/-- A factor `Y` that is measurable for a sub-σ-algebra `m` can be pulled out of the conditional
expectation of a conditional e-variable given `m`: `∫⁻ Y * X ∂P ≤ ∫⁻ Y ∂P`. -/
theorem IsCondEVar.lintegral_mul_le (hm : m ≤ mΩ) (hX : IsCondEVar X m S) (hP : P ∈ S)
    (hY : Measurable[m] Y) :
    ∫⁻ ω, Y ω * X ω ∂P ≤ ∫⁻ ω, Y ω ∂P := by
  simpa using lintegral_mul_le_lintegral_mul_of_forall_setLIntegral_le (g := 1) hm
    hX.measurable.aemeasurable aemeasurable_const
    (fun s hs ↦ by simpa using hX.setLIntegral_le P hP s hs) hY

/-- A factor `Y` that is measurable for a sub-σ-algebra `m` can be pulled out of the conditional
expectation of an exact conditional e-variable given `m`: `∫⁻ Y * X ∂P = ∫⁻ Y ∂P`. -/
theorem IsExactCondEVar.lintegral_mul_eq (hm : m ≤ mΩ) (hX : IsExactCondEVar X m S)
    (hP : P ∈ S) (hY : Measurable[m] Y) :
    ∫⁻ ω, Y ω * X ω ∂P = ∫⁻ ω, Y ω ∂P := by
  simpa using lintegral_mul_eq_lintegral_mul_of_forall_setLIntegral_eq (g := 1) hm
    hX.measurable.aemeasurable aemeasurable_const
    (fun s hs ↦ by simpa using hX.setLIntegral_eq P hP s hs) hY

/-- The set-integral form of `IsCondEVar.lintegral_mul_le`: for `m`-measurable `Y` and `s`,
`∫⁻ ω in s, Y ω * X ω ∂P ≤ ∫⁻ ω in s, Y ω ∂P`. -/
theorem IsCondEVar.setLIntegral_mul_le (hm : m ≤ mΩ) (hX : IsCondEVar X m S) (hP : P ∈ S)
    (hY : Measurable[m] Y) (hs : MeasurableSet[m] s) :
    ∫⁻ ω in s, Y ω * X ω ∂P ≤ ∫⁻ ω in s, Y ω ∂P := by
  rw [← lintegral_indicator (hm s hs), ← lintegral_indicator (hm s hs)]
  simp_rw [indicator_mul_left]
  exact hX.lintegral_mul_le hm hP (hY.indicator hs)

/-- The set-integral form of `IsExactCondEVar.lintegral_mul_eq`: for `m`-measurable `Y` and `s`,
`∫⁻ ω in s, Y ω * X ω ∂P = ∫⁻ ω in s, Y ω ∂P`. -/
theorem IsExactCondEVar.setLIntegral_mul_eq (hm : m ≤ mΩ) (hX : IsExactCondEVar X m S)
    (hP : P ∈ S) (hY : Measurable[m] Y) (hs : MeasurableSet[m] s) :
    ∫⁻ ω in s, Y ω * X ω ∂P = ∫⁻ ω in s, Y ω ∂P := by
  rw [← lintegral_indicator (hm s hs), ← lintegral_indicator (hm s hs)]
  simp_rw [indicator_mul_left]
  exact hX.lintegral_mul_eq hm hP (hY.indicator hs)

/-! ### Portfolios -/

/-- A portfolio of conditional e-variables given a sub-σ-algebra `m`, with `m`-measurable weights
`w ω i` summing to at most `1`, is a conditional e-variable given `m`. -/
theorem isCondEVar_sum_mul [Fintype ι] (hm : m ≤ mΩ) {E : ι → Ω → ℝ≥0∞} {w : Ω → ι → ℝ≥0∞}
    (hE : ∀ i, IsCondEVar (E i) m S) (hw : ∀ i, Measurable[m] (fun ω ↦ w ω i))
    (hw_sum : ∀ ω, ∑ i, w ω i ≤ 1) :
    IsCondEVar (fun ω ↦ ∑ i, w ω i * E i ω) m S := by
  have hwm (i : ι) : Measurable (fun ω ↦ w ω i) := (hw i).mono hm le_rfl
  refine ⟨Finset.measurable_fun_sum _ fun i _ ↦ (hwm i).mul (hE i).measurable,
    fun P hP s hs ↦ ?_⟩
  rw [lintegral_finsetSum (f := fun i ω ↦ w ω i * E i ω) _
    fun i _ ↦ (hwm i).mul (hE i).measurable]
  calc ∑ i, ∫⁻ ω in s, w ω i * E i ω ∂P
      ≤ ∑ i, ∫⁻ ω in s, w ω i ∂P :=
        Finset.sum_le_sum fun i _ ↦ (hE i).setLIntegral_mul_le hm hP (hw i) hs
    _ = ∫⁻ ω in s, ∑ i, w ω i ∂P := 
        (lintegral_finsetSum (f := fun i ω ↦ w ω i) _ fun i _ ↦ hwm i).symm
    _ ≤ ∫⁻ _ in s, 1 ∂P := lintegral_mono hw_sum
    _ = P s := by simp

/-- A portfolio of exact conditional e-variables given a sub-σ-algebra `m`, with `m`-measurable
weights `w ω i` summing to `1`, is an exact conditional e-variable given `m`. -/
theorem isExactCondEVar_sum_mul [Fintype ι] (hm : m ≤ mΩ) {E : ι → Ω → ℝ≥0∞}
    {w : Ω → ι → ℝ≥0∞} (hE : ∀ i, IsExactCondEVar (E i) m S)
    (hw : ∀ i, Measurable[m] (fun ω ↦ w ω i)) (hw_sum : ∀ ω, ∑ i, w ω i = 1) :
    IsExactCondEVar (fun ω ↦ ∑ i, w ω i * E i ω) m S := by
  have hwm (i : ι) : Measurable (fun ω ↦ w ω i) := (hw i).mono hm le_rfl
  refine ⟨Finset.measurable_fun_sum _ fun i _ ↦ (hwm i).mul (hE i).measurable,
    fun P hP s hs ↦ ?_⟩
  rw [lintegral_finsetSum (f := fun i ω ↦ w ω i * E i ω) _
    fun i _ ↦ (hwm i).mul (hE i).measurable]
  calc ∑ i, ∫⁻ ω in s, w ω i * E i ω ∂P
      = ∑ i, ∫⁻ ω in s, w ω i ∂P :=
        Finset.sum_congr rfl fun i _ ↦ (hE i).setLIntegral_mul_eq hm hP (hw i) hs
    _ = ∫⁻ ω in s, ∑ i, w ω i ∂P := 
        (lintegral_finsetSum (f := fun i ω ↦ w ω i) _ fun i _ ↦ hwm i).symm
    _ = P s := by simp [hw_sum]

end ProbabilityTheory
