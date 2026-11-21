/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.EValues.EProcess.Optimal
public import LMLExplore.EValues.Null.Basic
import LMLExplore.Probability.Process.StoppedValue

/-!
# E-processes that are optimal at a stopping time

On the space of stopped paths, e-processes for a null `S` are the e-variables of the stopped null
`stoppedNull ℱ S` (`isEProcess_iff_isEVar_stoppedNull`). An e-process `E` is *optimal at a
stopping time* `τ` against an alternative `Q` when `Function.uncurry E` is a numeraire of the
stopped null against the stopped law `stoppedLaw ℱ Q τ`: for a finite measure `Q`, `E` is an
e-process and `∫⁻ F_τ / E_τ ∂Q ≤ Q {0 < E_τ < ∞}` for every e-process `F`
(`isNumeraireAt_iff`), and `E` maximizes the expected logarithm at `τ` among the e-processes.
Such an e-process exists for every null of measures of mass at most one, with no dominating
measure, and its value at `τ` is almost surely unique.

For one stopping time `σ`, the values at `σ` of the e-processes are exactly the e-variables that
are measurable for the σ-algebra at `σ`, since `n ↦ Y · 𝟙{σ ≤ n}` is an e-process for every such
e-variable `Y` [EVR26, Note 40, Proposition 2]. Optimality at `σ` is therefore the optimality of
the value at `σ` for the null trimmed to the σ-algebra at `σ`, the image `mapNull id S` of the
null by the identity of `Ω` into `(Ω, hσ.measurableSpace)`, against the trimmed alternative
(`isNumeraireAt_iff_isNumeraire_mapNull`): the optimal e-process for one stopping time is the
numeraire of a null on one σ-algebra.

## Main definitions

* `ProbabilityTheory.IsNumeraireAt E ℱ S Q τ`: the e-process `E` for `S` is optimal at the time
  `τ` against `Q`.

## Main statements

* `ProbabilityTheory.isNumeraireAt_iff`: optimality at a measurable time, for instance a stopping
  time, in terms of the e-processes.
* `ProbabilityTheory.exists_isNumeraireAt`: for a null of measures of mass at most one and a finite
  alternative, some e-process is optimal at a given time.
* `ProbabilityTheory.IsNumeraireAt.eintegral_log_le`: an e-process that is optimal at a measurable
  time maximizes the expected logarithm at that time.
* `ProbabilityTheory.IsNumeraireAt.ae_eq`: two e-processes that are optimal at the same measurable
  time are almost surely equal at that time.
* `ProbabilityTheory.isEProcess_indicator_le`,
  `ProbabilityTheory.exists_isEProcess_apply_eq_iff`: the values at a stopping time `σ` of the
  e-processes are the e-variables that are measurable for the σ-algebra at `σ`.
* `ProbabilityTheory.isNumeraireAt_iff_isNumeraire_mapNull`: optimality at one stopping time is
  the optimality of the value at that time for the null trimmed to the σ-algebra at that time.

## Implementation notes

The definitions and statements are adapted from the file `notes/lean-wip/StoppedPaths.lean`
(commit `c6c6ba8`) of the paper project `RemyDegenne/evalues_research` (Apache 2.0), with the
stopped paths carrying Tau Ceti's progressive σ-algebra, and the class of the e-variables that are
measurable at `σ` replaced by the e-variables of the trimmed null.

## References

* [EVR26] *Answers to open questions in e-values and anytime-valid inference*, the notes and the
  Lean library `EValuesResearch` of github.com/RemyDegenne/evalues_research, 2026, Note 40.
* [KG22] W. M. Koolen and P. Grünwald, *Log-optimal anytime-valid e-values*, Int. J. Approx.
  Reason. 141 (2022), Section 3.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℕ mΩ} {S : Set (Measure Ω)}
  {Q : Measure Ω} {E F : ℕ → Ω → ℝ≥0∞} {τ σ : Ω → ℕ}

/-! ### Optimality at a stopping time -/

/-- The process `E` is **optimal at the time `τ`** for the null `S` against `Q`: on the space of
stopped paths, `Function.uncurry E` is a numeraire of the stopped null `stoppedNull ℱ S` against
the stopped law `stoppedLaw ℱ Q τ`. For a finite measure `Q` and a measurable time `τ`, this says
that `E` is an e-process and that `∫⁻ F_τ / E_τ ∂Q ≤ Q {0 < E_τ < ∞}` for every e-process `F`
(`isNumeraireAt_iff`). -/
def IsNumeraireAt (E : ℕ → Ω → ℝ≥0∞) (ℱ : Filtration ℕ mΩ) (S : Set (Measure Ω))
    (Q : Measure Ω) (τ : Ω → ℕ) : Prop :=
  IsNumeraire (m𝓧 := ℱ.progressive) (Function.uncurry E) (stoppedNull ℱ S) (stoppedLaw ℱ Q τ)

/-- Optimality at a time is the numeraire property on the space of stopped paths. -/
theorem isNumeraireAt_def :
    IsNumeraireAt E ℱ S Q τ ↔
      IsNumeraire (m𝓧 := ℱ.progressive) (Function.uncurry E) (stoppedNull ℱ S)
        (stoppedLaw ℱ Q τ) :=
  Iff.rfl

/-- A process that is optimal at some time is an e-process. -/
theorem IsNumeraireAt.isEProcess (hE : IsNumeraireAt E ℱ S Q τ) : IsEProcess E ℱ S :=
  isEProcess_iff_isEVar_stoppedNull.2 (isNumeraireAt_def.1 hE).isEVar

/-- **Optimality at a time, in terms of the e-processes.** Against a finite measure `Q`, a process
`E` is optimal at a measurable time `τ`, for instance a stopping time, exactly when it is an
e-process and `∫⁻ F_τ / E_τ ∂Q ≤ Q {0 < E_τ < ∞}` for every e-process `F`. -/
theorem isNumeraireAt_iff [IsFiniteMeasure Q] (hτ : Measurable τ) :
    IsNumeraireAt E ℱ S Q τ ↔ IsEProcess E ℱ S ∧ ∀ F : ℕ → Ω → ℝ≥0∞, IsEProcess F ℱ S →
      ∫⁻ ω, F (τ ω) ω / E (τ ω) ω ∂Q ≤ Q (fun ω ↦ E (τ ω) ω).fsupport := by
  rw [isNumeraireAt_def, isNumeraire_iff (m𝓧 := ℱ.progressive),
    ← isEProcess_iff_isEVar_stoppedNull]
  refine and_congr_right fun hE ↦ ?_
  have hEm := hE.measurable_uncurry
  rw [stoppedLaw_apply hτ (Measurable.measurable_fsupport (m𝓧 := ℱ.progressive) hEm)]
  refine ⟨fun h F hF ↦ ?_, fun h Y hY ↦ ?_⟩
  · have h' := h (isEProcess_iff_isEVar_stoppedNull.1 hF)
    rwa [lintegral_stoppedLaw hτ (f := fun x ↦ Function.uncurry F x /
      Function.uncurry E x) (hF.measurable_uncurry.div hEm)] at h'
  · rw [lintegral_stoppedLaw hτ (f := fun x ↦ Y x / Function.uncurry E x)
      (hY.measurable.div hEm)]
    rw [← Function.uncurry_curry Y] at hY
    exact h _ (isEProcess_iff_isEVar_stoppedNull.2 hY)

/-- **Existence of an optimal e-process at a given time.** For a null of measures of mass at most
one, with no dominating measure, a finite measure `Q` and any time `τ`, some e-process is optimal
at `τ` against `Q`. -/
theorem exists_isNumeraireAt (hS : ∀ P ∈ S, P univ ≤ 1) (Q : Measure Ω) [IsFiniteMeasure Q]
    (τ : Ω → ℕ) : ∃ E : ℕ → Ω → ℝ≥0∞, IsNumeraireAt E ℱ S Q τ := by
  obtain ⟨E, -, hE⟩ := exists_isEProcess_isNumeraire_stoppedNull hS (stoppedLaw ℱ Q τ)
  exact ⟨E, hE⟩

/-- **An optimal e-process maximizes the expected logarithm at its time.** If `E` is optimal at a
measurable time `τ` against `Q`, then `∫ᵉ log F_τ ∂Q ≤ ∫ᵉ log E_τ ∂Q` for every e-process `F`. -/
theorem IsNumeraireAt.eintegral_log_le (hE : IsNumeraireAt E ℱ S Q τ) (hF : IsEProcess F ℱ S)
    (hτ : Measurable τ) :
    ∫ᵉ ω, ENNReal.log (F (τ ω) ω) ∂Q ≤ ∫ᵉ ω, ENNReal.log (E (τ ω) ω) ∂Q := by
  have h := IsNumeraire.eintegral_log_le (m𝓧 := ℱ.progressive) hE
    (isEProcess_iff_isEVar_stoppedNull.1 hF)
  have hlog {G : ℕ → Ω → ℝ≥0∞} (hG : IsEProcess G ℱ S) :
      Measurable[ℱ.progressive] fun x ↦ (ENNReal.log (Function.uncurry G x) : EReal) :=
    ENNReal.measurable_log.comp hG.measurable_uncurry
  rwa [eintegral_stoppedLaw hτ (hlog hF), eintegral_stoppedLaw hτ (hlog hE.isEProcess)] at h

/-- Two processes that are optimal at the same measurable time are almost surely equal at that
time. -/
theorem IsNumeraireAt.ae_eq (hE : IsNumeraireAt E ℱ S Q τ) (hF : IsNumeraireAt F ℱ S Q τ)
    (hτ : Measurable τ) :
    ∀ᵐ ω ∂Q, E (τ ω) ω = F (τ ω) ω := by
  have h := IsNumeraire.ae_unique (m𝓧 := ℱ.progressive) hE hF
  refine (ae_stoppedLaw_iff hτ
    (p := fun x ↦ Function.uncurry E x = Function.uncurry F x) ?_).1 h
  exact measurableSet_eq_fun (m := ℱ.progressive) hE.isEProcess.measurable_uncurry
    hF.isEProcess.measurable_uncurry

/-- A process that is optimal at a measurable time is almost surely infinite at that time where
some e-process is infinite. -/
theorem IsNumeraireAt.ae_eq_top_of_eq_top (hE : IsNumeraireAt E ℱ S Q τ) (hF : IsEProcess F ℱ S)
    (hτ : Measurable τ) :
    ∀ᵐ ω ∂Q, F (τ ω) ω = ∞ → E (τ ω) ω = ∞ := by
  have h := IsNumeraire.ae_eq_top_of_eq_top (m𝓧 := ℱ.progressive) hE
    (isEProcess_iff_isEVar_stoppedNull.1 hF)
  refine (ae_stoppedLaw_iff hτ
    (p := fun x ↦ Function.uncurry F x = ∞ → Function.uncurry E x = ∞) ?_).1 h
  simp only [imp_iff_not_or, ofPred_or]
  exact (hF.measurable_uncurry (measurableSet_singleton ∞)).compl.union
    (hE.isEProcess.measurable_uncurry (measurableSet_singleton ∞))

/-! ### One stopping time -/

/-- **An e-variable known at a stopping time is the value of an e-process**
[EVR26, Note 40, Proposition 2]. For a stopping time `σ` with values in `ℕ` and an e-variable `Y`
that is measurable for the σ-algebra at `σ`, the process `n ↦ Y · 𝟙{σ ≤ n}` is an e-process. Its
value at `σ` is `Y`. -/
theorem isEProcess_indicator_le (hσ : IsStoppingTime ℱ fun ω ↦ (σ ω : WithTop ℕ))
    {Y : Ω → ℝ≥0∞} (hY : IsEVar Y S) (hYσ : Measurable[hσ.measurableSpace] Y) :
    IsEProcess (fun n ↦ {ω | σ ω ≤ n}.indicator Y) ℱ S := by
  have h_ad : Adapted ℱ fun n ↦ {ω | σ ω ≤ n}.indicator Y := by
    intro n t ht
    rw [indicator_preimage, Set.ite]
    have h_le : {ω | σ ω ≤ n} = {ω | (σ ω : WithTop ℕ) ≤ n} := by
      ext ω
      simp
    rw [h_le]
    exact (((hσ.measurableSet _).1 (hYσ ht)).2 n).union
      ((@measurable_const ℝ≥0∞ Ω _ (ℱ n) 0 t ht).diff (hσ.measurableSet_le_natCast n))
  exact ⟨h_ad, fun τ hτ ↦ hY.mono (h_ad.measurable_apply_stoppingTime hτ)
    fun ω ↦ indicator_le_self _ _ ω⟩

/-- **The values at a stopping time of the e-processes** [EVR26, Note 40, Proposition 2]. For a
stopping time `σ` with values in `ℕ`, a function is the value at `σ` of an e-process exactly when
it is an e-variable that is measurable for the σ-algebra at `σ`. -/
theorem exists_isEProcess_apply_eq_iff (hσ : IsStoppingTime ℱ fun ω ↦ (σ ω : WithTop ℕ))
    {Y : Ω → ℝ≥0∞} :
    (∃ E : ℕ → Ω → ℝ≥0∞, IsEProcess E ℱ S ∧ (fun ω ↦ E (σ ω) ω) = Y) ↔
      IsEVar Y S ∧ Measurable[hσ.measurableSpace] Y := by
  refine ⟨?_, fun ⟨hY, hYσ⟩ ↦ ⟨_, isEProcess_indicator_le hσ hY hYσ, funext fun ω ↦ ?_⟩⟩
  · rintro ⟨E, hE, rfl⟩
    exact ⟨hE.isEVar_stoppedValue σ hσ, hE.adapted.measurable_measurableSpace_apply_stoppingTime hσ⟩
  · simp

/-- **Optimality at one stopping time** [EVR26, Note 40, Proposition 2]. Against a finite measure
`Q`, an e-process `E` is optimal at a stopping time `σ` with values in `ℕ` exactly when its value
at `σ` is the numeraire of the null trimmed to the σ-algebra at `σ`, the image `mapNull id S` of
the null by the identity of `Ω` into `(Ω, hσ.measurableSpace)`, against the trimmed measure. -/
theorem isNumeraireAt_iff_isNumeraire_mapNull [IsFiniteMeasure Q]
    (hσ : IsStoppingTime ℱ fun ω ↦ (σ ω : WithTop ℕ)) (hE : IsEProcess E ℱ S) :
    IsNumeraireAt E ℱ S Q σ ↔
      IsNumeraire (m𝓧 := hσ.measurableSpace) (fun ω ↦ E (σ ω) ω)
        (@mapNull _ _ _ hσ.measurableSpace id S) (Q.trim hσ.measurableSpace_le) := by
  have hEσ := hE.adapted.measurable_measurableSpace_apply_stoppingTime hσ
  rw [isNumeraireAt_iff hσ.measurable_nat, isNumeraire_iff (m𝓧 := hσ.measurableSpace),
    isEVar_mapNull_id_iff hσ.measurableSpace_le,
    trim_measurableSet_eq _ (Measurable.measurable_fsupport (m𝓧 := hσ.measurableSpace) hEσ)]
  simp only [hE, true_and, hE.isEVar_stoppedValue σ hσ, hEσ, and_self]
  refine ⟨fun h Y hY ↦ ?_, fun h F hF ↦ ?_⟩
  · rw [isEVar_mapNull_id_iff hσ.measurableSpace_le] at hY
    rw [lintegral_trim _ (f := fun ω ↦ Y ω / E (σ ω) ω) (hY.2.div hEσ)]
    refine le_of_eq_of_le (lintegral_congr fun ω ↦ ?_) (h _ (isEProcess_indicator_le hσ hY.1 hY.2))
    simp
  · have hFσ := hF.adapted.measurable_measurableSpace_apply_stoppingTime hσ
    rw [← lintegral_trim hσ.measurableSpace_le (f := fun ω ↦ F (σ ω) ω / E (σ ω) ω)
      (hFσ.div hEσ)]
    exact h ((isEVar_mapNull_id_iff hσ.measurableSpace_le).2 ⟨hF.isEVar_stoppedValue σ hσ, hFσ⟩)

end ProbabilityTheory
