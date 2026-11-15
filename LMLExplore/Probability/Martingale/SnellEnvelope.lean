/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.MeasureTheory.Function.ConditionalLExpectation
public import LMLExplore.MeasureTheory.Function.EssSupFamily
public import LMLExplore.Probability.Martingale.OptionalStopping
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.LebesgueBochner

/-!
# The Snell envelope in discrete time

For a process `E : ℕ → Ω → ℝ≥0∞`, a filtration `ℱ` indexed by `ℕ` and a measure `P`, the
**Snell envelope** of `E` at time `n` is the essential supremum, over the bounded stopping times
`τ ≥ n` with values in `ℕ`, of the conditional expectations given `ℱ n` of the values `E τ` of
the process at `τ`. It is the value at time `n` of optimal stopping after `n`, and, for an adapted
process, the smallest `ℝ≥0∞`-valued supermartingale that dominates it.

The conditional expectations are Mathlib's conditional Lebesgue expectations `P⁻[X|m]` of
`ℝ≥0∞`-valued functions, and the essential supremum is `MeasureTheory.essSupFamily`. Neither needs
integrability, so the Snell envelope is defined and is a supermartingale for every process. When
the values of the process are measurable with finite expectations, it agrees almost surely with
the essential supremum of the conditional expectations `P[(E τ).toReal|ℱ n]` of the real values
(`ProbabilityTheory.snellEnvelope_ae_eq_essSupFamily_condExp`).

Its role in anytime-valid inference is the characterization of e-processes: an adapted process
whose values at all bounded stopping times have expectation at most `1` under `P` is dominated by
a test supermartingale for `P`, its Snell envelope [RRLK, Lemma 6, Appendix A].

The proofs follow the essential supremum description of the Snell envelope [FS16, Chapter 6]. The
family of conditional expectations at the bounded stopping times after `n` is directed upward,
since pasting two such stopping times along the set where one of their conditional expectations
is the larger gives another one. So the set integrals of the Snell envelope are the suprema of the
set integrals of the process at those stopping times, from which the supermartingale property and
the expectation at time `0` follow; minimality is optional stopping for bounded stopping times.

## Main definitions

* `ProbabilityTheory.boundedStoppingTimesFrom ℱ n`: the bounded `ℕ`-valued stopping times after
  `n`, which index the Snell envelope at time `n`.
* `ProbabilityTheory.snellEnvelope E ℱ P`: the Snell envelope of `E`.

## Main statements

* `ProbabilityTheory.condLExp_ae_le_snellEnvelope`, `ProbabilityTheory.snellEnvelope_ae_le`,
  `ProbabilityTheory.snellEnvelope_ae_le_iff`: the Snell envelope at time `n` is the almost
  everywhere least function above the conditional expectations at the bounded stopping times
  after `n`.
* `ProbabilityTheory.ae_le_snellEnvelope`: the Snell envelope of an adapted process dominates it.
* `ProbabilityTheory.setLIntegral_snellEnvelope`: its integral over an `ℱ n`-measurable set is the
  supremum of the integrals of the process at the bounded stopping times after `n`, and
  `ProbabilityTheory.lintegral_snellEnvelope_zero`: its expectation at time `0` is
  `⨆ τ, ∫⁻ E τ ∂P` over the bounded stopping times.
* `ProbabilityTheory.isENNSupermartingale_snellEnvelope`: it is an `ℝ≥0∞`-valued supermartingale,
  and `ProbabilityTheory.IsENNSupermartingale.snellEnvelope_ae_le`: it is below every
  `ℝ≥0∞`-valued supermartingale that dominates the process.
* `ProbabilityTheory.isTestSupermartingale_snellEnvelope`: it is a test supermartingale when the
  expectations of the process at bounded stopping times are at most `1`.

## References

* [FS16] H. Föllmer and A. Schied, *Stochastic Finance: An Introduction in Discrete Time*,
  4th edition, De Gruyter, 2016, Chapter 6.
* [RRLK] A. Ramdas, J. Ruf, M. Larsson and W. M. Koolen, *Admissible anytime-valid sequential
  inference must rely on nonnegative martingales*, arXiv:2009.03167v3, Lemma 6 and Appendix A.
-/

public section

open MeasureTheory Filter Set
open scoped ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℕ mΩ} {P : Measure Ω}
  {S : Set (Measure Ω)} {E M : ℕ → Ω → ℝ≥0∞} {τ τ₁ τ₂ : Ω → ℕ} {n : ℕ} {h : Ω → ℝ≥0∞}

/-! ### Bounded stopping times after a time -/

/-- The **bounded stopping times after `n`** of a filtration `ℱ` indexed by `ℕ`: the stopping
times `τ` with values in `ℕ` that are at least `n` and bounded by a constant. -/
def boundedStoppingTimesFrom (ℱ : Filtration ℕ mΩ) (n : ℕ) : Set (Ω → ℕ) :=
  {τ | (IsStoppingTime ℱ fun ω ↦ (τ ω : WithTop ℕ)) ∧ (∀ ω, n ≤ τ ω) ∧ ∃ N : ℕ, ∀ ω, τ ω ≤ N}

/-- Membership in `boundedStoppingTimesFrom ℱ n`, unfolded. -/
@[simp]
theorem mem_boundedStoppingTimesFrom_iff :
    τ ∈ boundedStoppingTimesFrom ℱ n ↔
      (IsStoppingTime ℱ fun ω ↦ (τ ω : WithTop ℕ)) ∧ (∀ ω, n ≤ τ ω) ∧ ∃ N : ℕ, ∀ ω, τ ω ≤ N :=
  Iff.rfl

/-- The constant time `n` is a bounded stopping time after `n`. -/
theorem const_mem_boundedStoppingTimesFrom (ℱ : Filtration ℕ mΩ) (n : ℕ) :
    (fun _ : Ω ↦ n) ∈ boundedStoppingTimesFrom ℱ n :=
  ⟨isStoppingTime_natCast n, fun _ ↦ le_rfl, n, fun _ ↦ le_rfl⟩

/-- A bounded stopping time after a time `n` is a bounded stopping time after every earlier
time. -/
theorem boundedStoppingTimesFrom_anti (ℱ : Filtration ℕ mΩ) :
    Antitone (boundedStoppingTimesFrom ℱ) := fun _ _ hmn _ ⟨hτ, hnτ, hτN⟩ ↦
  ⟨hτ, fun ω ↦ hmn.trans (hnτ ω), hτN⟩

/-- Pasting two bounded stopping times after `n` along an `ℱ n`-measurable set gives a bounded
stopping time after `n`. -/
theorem piecewise_mem_boundedStoppingTimesFrom {A : Set Ω} [DecidablePred (· ∈ A)]
    (hA : MeasurableSet[ℱ n] A) (hτ₁ : τ₁ ∈ boundedStoppingTimesFrom ℱ n)
    (hτ₂ : τ₂ ∈ boundedStoppingTimesFrom ℱ n) :
    A.piecewise τ₁ τ₂ ∈ boundedStoppingTimesFrom ℱ n := by
  obtain ⟨hτ₁, hnτ₁, N₁, hτN₁⟩ := hτ₁
  obtain ⟨hτ₂, hnτ₂, N₂, hτN₂⟩ := hτ₂
  refine ⟨?_, fun ω ↦ ?_, max N₁ N₂, fun ω ↦ ?_⟩
  · have h := hτ₁.piecewise_of_le hτ₂ (i := n)
      (fun ω ↦ by rw [← Nat.cast_withTop]; exact_mod_cast hnτ₁ ω)
      (fun ω ↦ by rw [← Nat.cast_withTop]; exact_mod_cast hnτ₂ ω) hA
    convert h using 1
    funext ω
    by_cases hω : ω ∈ A <;> simp [hω]
  · by_cases hω : ω ∈ A <;> simp [hω, hnτ₁, hnτ₂]
  · by_cases hω : ω ∈ A <;> simp [hω, hτN₁, hτN₂]

/-! ### The Snell envelope -/

/-- The **Snell envelope** of a process `E : ℕ → Ω → ℝ≥0∞` for a filtration `ℱ` and a measure
`P`: at time `n`, the essential supremum under `P`, over the bounded stopping times `τ` after `n`
(`ProbabilityTheory.boundedStoppingTimesFrom ℱ n`), of the conditional expectation
`P⁻[E τ|ℱ n]` of the value of the process at `τ`. -/
noncomputable def snellEnvelope (E : ℕ → Ω → ℝ≥0∞) (ℱ : Filtration ℕ mΩ) (P : Measure Ω)
    (n : ℕ) : Ω → ℝ≥0∞ :=
  essSupFamily (fun τ : boundedStoppingTimesFrom ℱ n ↦ P⁻[fun ω ↦ E (τ.1 ω) ω|ℱ n]) P

/-- The defining equation of `snellEnvelope`. -/
theorem snellEnvelope_def (E : ℕ → Ω → ℝ≥0∞) (ℱ : Filtration ℕ mΩ) (P : Measure Ω) (n : ℕ) :
    snellEnvelope E ℱ P n =
      essSupFamily (fun τ : boundedStoppingTimesFrom ℱ n ↦ P⁻[fun ω ↦ E (τ.1 ω) ω|ℱ n]) P :=
  (rfl)

/-- The Snell envelope is adapted, for every process. -/
theorem adapted_snellEnvelope (E : ℕ → Ω → ℝ≥0∞) (ℱ : Filtration ℕ mΩ) (P : Measure Ω) :
    Adapted ℱ (snellEnvelope E ℱ P) := fun _ ↦
  measurable_essSupFamily fun _ ↦ measurable_condLExp _ _ _

/-- The Snell envelope at time `n` dominates almost everywhere the conditional expectation given
`ℱ n` of the value of the process at every bounded stopping time `τ` after `n`. -/
theorem condLExp_ae_le_snellEnvelope [SigmaFiniteFiltration P ℱ]
    (hτ : τ ∈ boundedStoppingTimesFrom ℱ n) :
    P⁻[fun ω ↦ E (τ ω) ω|ℱ n] ≤ᵐ[P] snellEnvelope E ℱ P n := by
  have := SigmaFinite.of_trim (μ := P) (ℱ.le n)
  rw [snellEnvelope_def]
  exact ae_le_essSupFamily (μ := P)
    (fun τ : boundedStoppingTimesFrom ℱ n ↦
      (measurable_condLExp' (ℱ n) P fun ω ↦ E (τ.1 ω) ω).aemeasurable) ⟨τ, hτ⟩

/-- The Snell envelope at time `n` is almost everywhere below every function that dominates
almost everywhere the conditional expectations given `ℱ n` of the values of the process at the
bounded stopping times `τ` after `n`. -/
theorem snellEnvelope_ae_le
    (hh : ∀ τ ∈ boundedStoppingTimesFrom ℱ n, P⁻[fun ω ↦ E (τ ω) ω | ℱ n] ≤ᵐ[P] h) :
    snellEnvelope E ℱ P n ≤ᵐ[P] h :=
  essSupFamily_ae_le fun τ ↦ hh τ.1 τ.2

/-- A function dominates the Snell envelope at time `n` almost everywhere exactly when it
dominates almost everywhere the conditional expectations given `ℱ n` of the values of the process
at the bounded stopping times `τ` after `n`. -/
theorem snellEnvelope_ae_le_iff [SigmaFiniteFiltration P ℱ] :
    snellEnvelope E ℱ P n ≤ᵐ[P] h ↔
      ∀ τ ∈ boundedStoppingTimesFrom ℱ n, P⁻[fun ω ↦ E (τ ω) ω|ℱ n] ≤ᵐ[P] h :=
  ⟨fun hh _ hτ ↦ (condLExp_ae_le_snellEnvelope hτ).trans hh, snellEnvelope_ae_le⟩

/-- The Snell envelope of an adapted process dominates it almost everywhere at every time. -/
theorem ae_le_snellEnvelope [SigmaFiniteFiltration P ℱ] (hE : Adapted ℱ E) (n : ℕ) :
    E n ≤ᵐ[P] snellEnvelope E ℱ P n := by
  have h := condLExp_ae_le_snellEnvelope (E := E) (P := P)
    (const_mem_boundedStoppingTimesFrom ℱ n)
  rwa [condLExp_eq_self (ℱ.le n) P (hE n)] at h

/-- The conditional expectations given `ℱ n` of the values of a process at the bounded stopping
times `τ` after `n` form a family directed upward almost everywhere: pasting two stopping times
along the `ℱ n`-measurable set where the first conditional expectation is the larger gives a
bounded stopping time after `n` whose conditional expectation is the maximum of the two. -/
private theorem directed_condLExp [SigmaFiniteFiltration P ℱ] (E : ℕ → Ω → ℝ≥0∞) (n : ℕ) :
    Directed (· ≤ᵐ[P] ·)
      (fun τ : boundedStoppingTimesFrom ℱ n ↦ P⁻[fun ω ↦ E (τ.1 ω) ω|ℱ n]) := by
  classical
  rintro ⟨τ₁, hτ₁⟩ ⟨τ₂, hτ₂⟩
  set A := {ω | P⁻[fun ω ↦ E (τ₂ ω) ω|ℱ n] ω ≤ P⁻[fun ω ↦ E (τ₁ ω) ω|ℱ n] ω}
  have hA : MeasurableSet[ℱ n] A :=
    measurableSet_le (measurable_condLExp _ _ _) (measurable_condLExp _ _ _)
  have hpw : (fun ω ↦ E (A.piecewise τ₁ τ₂ ω) ω) =
      A.piecewise (fun ω ↦ E (τ₁ ω) ω) (fun ω ↦ E (τ₂ ω) ω) := by
    funext ω
    by_cases hω : ω ∈ A <;> simp [hω]
  have h_eq := condLExp_piecewise (P := P) (ℱ.le n) hA (fun ω ↦ E (τ₁ ω) ω) (fun ω ↦ E (τ₂ ω) ω)
  refine ⟨⟨A.piecewise τ₁ τ₂, piecewise_mem_boundedStoppingTimesFrom hA hτ₁ hτ₂⟩, ?_, ?_⟩
  · filter_upwards [h_eq] with ω hω
    simp only [hpw, hω]
    by_cases hωA : ω ∈ A
    · rw [piecewise_eq_of_mem _ _ _ hωA]
    · rw [piecewise_eq_of_notMem _ _ _ hωA]
      exact (not_le.1 hωA).le
  · filter_upwards [h_eq] with ω hω
    simp only [hpw, hω]
    by_cases hωA : ω ∈ A
    · rw [piecewise_eq_of_mem _ _ _ hωA]
      exact hωA
    · rw [piecewise_eq_of_notMem _ _ _ hωA]

/-- The integral of the Snell envelope at time `n` over an `ℱ n`-measurable set `s` is the
supremum of the integrals over `s` of the process at the bounded stopping times `τ` after `n`. -/
theorem setLIntegral_snellEnvelope [SigmaFiniteFiltration P ℱ] {s : Set Ω}
    (hs : MeasurableSet[ℱ n] s) :
    ∫⁻ ω in s, snellEnvelope E ℱ P n ω ∂P =
      ⨆ τ ∈ boundedStoppingTimesFrom ℱ n, ∫⁻ ω in s, E (τ ω) ω ∂P := by
  have := SigmaFinite.of_trim (μ := P) (ℱ.le n)
  rw [snellEnvelope_def, setLIntegral_essSupFamily_of_directed
    (fun _ ↦ (measurable_condLExp' _ _ _).aemeasurable) (directed_condLExp (P := P) (ℱ := ℱ) E n)]
  simp only [iSup_subtype, setLIntegral_condLExp (ℱ.le n) P _ hs]

/-- The expectation of the Snell envelope at time `0` is the supremum of the expectations of the
process at the bounded stopping times. -/
theorem lintegral_snellEnvelope_zero [SigmaFiniteFiltration P ℱ] :
    ∫⁻ ω, snellEnvelope E ℱ P 0 ω ∂P =
      ⨆ τ ∈ boundedStoppingTimesFrom ℱ 0, ∫⁻ ω, E (τ ω) ω ∂P := by
  simpa only [Measure.restrict_univ] using
    setLIntegral_snellEnvelope (E := E) (P := P) (n := 0) MeasurableSet.univ

/-- The Snell envelope of every process is an `ℝ≥0∞`-valued supermartingale. -/
theorem isENNSupermartingale_snellEnvelope [SigmaFiniteFiltration P ℱ] (E : ℕ → Ω → ℝ≥0∞) :
    IsENNSupermartingale (snellEnvelope E ℱ P) ℱ {P} := by
  refine ⟨adapted_snellEnvelope E ℱ P, fun Q hQ n s hs ↦ ?_⟩
  rw [mem_singleton_iff.1 hQ, setLIntegral_snellEnvelope (ℱ.mono n.le_succ s hs),
    setLIntegral_snellEnvelope hs]
  -- The stopping times after `n + 1` are among those after `n`.
  exact biSup_mono fun _ hτ ↦ boundedStoppingTimesFrom_anti ℱ n.le_succ hτ

/-- **Minimality of the Snell envelope.** The Snell envelope for `P ∈ S` is almost everywhere
below every `ℝ≥0∞`-valued supermartingale for `S` that dominates the process almost everywhere
under `P` at every time. -/
theorem IsENNSupermartingale.snellEnvelope_ae_le [SigmaFiniteFiltration P ℱ]
    (hM : IsENNSupermartingale M ℱ S) (hP : P ∈ S) (hEM : ∀ n, E n ≤ᵐ[P] M n) (n : ℕ) :
    snellEnvelope E ℱ P n ≤ᵐ[P] M n := by
  refine ProbabilityTheory.snellEnvelope_ae_le fun τ ⟨hτ, hnτ, N, hτN⟩ ↦ ?_
  rw [condLExp_ae_le_iff_forall_setLIntegral_le (ℱ.le n) (hM.adapted n)]
  intro s hs
  have hEM' : ∀ᵐ ω ∂P, ∀ k, E k ω ≤ M k ω := ae_all_iff.2 hEM
  calc ∫⁻ ω in s, E (τ ω) ω ∂P ≤ ∫⁻ ω in s, M (τ ω) ω ∂P :=
        lintegral_mono_ae (ae_restrict_of_ae (hEM'.mono fun ω hω ↦ hω (τ ω)))
    _ ≤ ∫⁻ ω in s, M n ω ∂P := by
        -- Optional stopping between the constant time `n` and `τ`.
        have h := hM.setLIntegral_stoppedValueLimsup_le_of_le_const hP
          (isStoppingTime_natCast n) hτ (fun ω ↦ by exact_mod_cast hnτ ω) (N := N)
          (fun ω ↦ by exact_mod_cast hτN ω) (s := s)
          ((isStoppingTime_natCast n).le_measurableSpace_of_const_le
            (fun _ ↦ (Nat.cast_withTop n).symm.le) s hs)
        rwa [stoppedValueLimsup_natCast, stoppedValueLimsup_const] at h

/-- The Snell envelope of a process whose expectations at the bounded stopping times are at most
`1` under `P` is a test supermartingale for `P`. -/
theorem isTestSupermartingale_snellEnvelope [SigmaFiniteFiltration P ℱ]
    (hE : ∀ τ ∈ boundedStoppingTimesFrom ℱ 0, ∫⁻ ω, E (τ ω) ω ∂P ≤ 1) :
    IsTestSupermartingale (snellEnvelope E ℱ P) ℱ {P} :=
  ⟨isENNSupermartingale_snellEnvelope E, fun Q hQ ↦ by
    rw [mem_singleton_iff.1 hQ, lintegral_snellEnvelope_zero]
    exact iSup₂_le hE⟩

/-- For a process of measurable functions with finite expectations, the Snell envelope agrees
almost everywhere with the essential supremum, over the bounded stopping times `τ` after `n`, of
the conditional expectations `P[(E τ).toReal|ℱ n]` of the real values of the process at `τ`, the
form in which it is classically defined. -/
theorem snellEnvelope_ae_eq_essSupFamily_condExp [SigmaFiniteFiltration P ℱ]
    (hE : ∀ n, Measurable (E n)) (hE_int : ∀ n, ∫⁻ ω, E n ω ∂P ≠ ∞) (n : ℕ) :
    snellEnvelope E ℱ P n =ᵐ[P]
      essSupFamily (fun τ : boundedStoppingTimesFrom ℱ n ↦
        fun ω ↦ ENNReal.ofReal (P[fun ω ↦ (E (τ.1 ω) ω).toReal|ℱ n] ω)) P := by
  have := SigmaFinite.of_trim (μ := P) (ℱ.le n)
  have h (τ : boundedStoppingTimesFrom ℱ n) :
      P⁻[fun ω ↦ E (τ.1 ω) ω|ℱ n] =ᵐ[P]
        fun ω ↦ ENNReal.ofReal (P[fun ω ↦ (E (τ.1 ω) ω).toReal|ℱ n] ω) := by
    obtain ⟨τ, hτ, -, N, hτN⟩ := τ
    have hmeas : Measurable fun ω ↦ E (τ ω) ω := by
      simpa using measurable_stoppedValueLimsup hE hτ.measurable'
    -- The value at `τ ≤ N` is below the sum of the values at the times up to `N`.
    have hle := lintegral_stoppedValueLimsup_le_sum (μ := P) (fun k ↦ (hE k).aemeasurable)
      (τ := fun ω ↦ (τ ω : WithTop ℕ)) (N := N) fun ω ↦ by exact_mod_cast hτN ω
    rw [stoppedValueLimsup_natCast] at hle
    have hint : ∫⁻ ω, E (τ ω) ω ∂P ≠ ∞ :=
      ne_top_of_le_ne_top (ENNReal.sum_ne_top.2 fun k _ ↦ hE_int k) hle
    filter_upwards [toReal_condLExp (ℱ n) hmeas.aemeasurable hint,
      condLExp_ne_top (mΩ := ℱ n) hint] with ω h₁ h₂
    rw [← h₁, ENNReal.ofReal_toReal h₂]
  rw [snellEnvelope_def]
  exact (essSupFamily_mono_ae (fun _ ↦ integrable_condExp.aemeasurable.ennreal_ofReal)
    fun τ ↦ (h τ).le).antisymm (essSupFamily_mono_ae
      (fun _ ↦ (measurable_condLExp' _ _ _).aemeasurable) fun τ ↦ (h τ).symm.le)

end ProbabilityTheory
