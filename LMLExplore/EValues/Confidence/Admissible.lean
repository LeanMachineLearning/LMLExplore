/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.EValues.Confidence.Sequence

/-!
# Admissible confidence sequences

A confidence sequence `D` at level `α` for the nulls `S : Θ → Set (Measure Ω)` dominates a
confidence sequence `C` when `D n ⊆ C n` at every time `n`, almost surely under every law of the
model `⋃ θ, S θ`, and dominates it strictly when moreover `D n` is a strict subset of `C n` at
some time with positive probability under some law of the model. A confidence sequence is
admissible when no confidence sequence dominates it strictly [RRLK, §4.3]: every confidence
sequence that dominates it is almost surely equal to it at every time, under every law of the
model. As for e-processes and sequential tests, this is the admissibility `Filter.IsAdmissible`
for the quasi-sure order of the model, here of the sets `(C n ω)ᶜ` of the rejected parameters.

Admissibility of confidence sequences reduces to that of the sequential tests of the duality
between them [RRLK, Theorem 30]. The test `𝟙{θ ∉ C n}` of each null `S θ` read off an admissible
confidence sequence `C` is admissible, for any type of parameters and any family of nulls.
Conversely, the parameters not rejected by a family of admissible level-`α` sequential tests form
an admissible confidence sequence, when the parameters are countable and every event of time `n`
that is null under every law of `S θ` is null under every law of the model: [RRLK] assumes the
second condition throughout (its standing assumption of §4.2). Neither condition can be dropped.
At level `0` the constant tests `0` are admissible, and their confidence sequence is the constant
set of all parameters. For the parameters `Θ = ℝ`, the same null `S θ = {P}` for every `θ`, for a
probability measure `P`, so that the second condition holds, and an `ℱ 0`-measurable random
parameter `U` with no atom under `P`, the confidence sequence `ℝ \ {U}` improves on it, although
each of its tests differs from `0` only on a `P`-null set. For two parameters whose nulls are
the point masses `{δ a}` and `{δ b}` on a two-point space `{a, b}`, the confidence sequence that is
`{0}` at `a` and `{1}` at `b` improves on it, since the event `{b}` is null for the first null but
not for the model.

With the sufficient condition for admissible sequential tests, this gives admissible confidence
sequences from test supermartingales `M θ` for the nulls `S θ` that reach `α⁻¹` with probability
exactly `α` under the laws of `S θ`: the parameters `θ` for which `M θ` has stayed below `α⁻¹`
[RRLK, Theorem 30 (2)].

## Main definitions

* `ProbabilityTheory.IsAdmissibleConfSeq C ℱ S α`: `C` is an admissible confidence sequence at
  level `α` for the parameters of the nulls `S` and the filtration `ℱ`.

## Main statements

* `ProbabilityTheory.isAdmissibleConfSeq_iff`: a confidence sequence is admissible exactly when
  every confidence sequence that is almost surely contained in it at every time almost surely
  contains it at every time, under every law of the model.
* `ProbabilityTheory.IsAdmissibleConfSeq.isAdmissibleSequentialTest`: the tests of the nulls read
  off an admissible confidence sequence are admissible [RRLK, Theorem 30].
* `ProbabilityTheory.isAdmissibleConfSeq_of_isAdmissibleSequentialTest`: the parameters not
  rejected by admissible sequential tests form an admissible confidence sequence, for countably
  many parameters with nulls that see the null events of the model [RRLK, Theorem 30].
* `ProbabilityTheory.isAdmissibleConfSeq_iff_forall_isAdmissibleSequentialTest`: under the same
  conditions, a confidence sequence is admissible exactly when its tests are admissible
  [RRLK, Theorem 30].
* `ProbabilityTheory.isAdmissibleConfSeq_of_isTestSupermartingale`: admissible confidence
  sequences from test supermartingales for which Ville's inequality is an equality
  [RRLK, Theorem 30 (2)].

## References

* [RRLK] A. Ramdas, J. Ruf, M. Larsson and W. M. Koolen, *Admissible anytime-valid sequential
  inference must rely on nonnegative martingales*, arXiv:2009.03167v3, §4.2, §4.3 and Theorem 30.
-/

public section

open MeasureTheory Filter Set
open scoped ENNReal

namespace ProbabilityTheory

variable {Ω Θ : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℕ mΩ}
  {S : Θ → Set (Measure Ω)} {C : ℕ → Ω → Set Θ} {α : ℝ≥0∞}

/-- A confidence sequence `C` at level `α` for the parameters of the nulls `S` and the filtration
`ℱ` is **admissible** when every confidence sequence at level `α` that is contained in `C`
quasi-surely for the model `⋃ θ, S θ`, at every time, contains `C` quasi-surely at every time:
no confidence sequence dominates `C` strictly [RRLK, §4.3] (`isAdmissibleConfSeq_iff`). It is the
admissibility (`Filter.IsAdmissible`) of the sets of rejected parameters
`ω ↦ (n ↦ (C n ω)ᶜ)`, larger being better, among those of confidence sequences at level `α`, for
the quasi-sure order of the model. -/
abbrev IsAdmissibleConfSeq (C : ℕ → Ω → Set Θ) (ℱ : Filtration ℕ mΩ) (S : Θ → Set (Measure Ω))
    (α : ℝ≥0∞) : Prop :=
  (quasiSure (⋃ θ, S θ)).IsAdmissible
    {R : Ω → ℕ → Set Θ | IsConfSeq (fun n ω ↦ (R ω n)ᶜ) ℱ S α}
    fun ω n ↦ (C n ω)ᶜ

/-- A confidence sequence is admissible exactly when every confidence sequence at the same level
that is contained in it quasi-surely for the model at every time contains it quasi-surely for the
model at every time. -/
theorem isAdmissibleConfSeq_iff :
    IsAdmissibleConfSeq C ℱ S α ↔ IsConfSeq C ℱ S α ∧ ∀ D, IsConfSeq D ℱ S α →
      (∀ n, ∀ᶠ ω in quasiSure (⋃ θ, S θ), D n ω ⊆ C n ω) →
        ∀ n, ∀ᶠ ω in quasiSure (⋃ θ, S θ), C n ω ⊆ D n ω := by
  -- admissibility compares the processes of rejected sets `n ↦ (C n)ᶜ` at every time, and the
  -- rejected sets of `D` contain those of `C` exactly when `D ⊆ C`
  refine (Filter.isAdmissible_swap_iff (p := fun R ↦ IsConfSeq (fun n ω ↦ (R n ω)ᶜ) ℱ S α)
    (f := fun n ω ↦ (C n ω)ᶜ)).trans ⟨fun ⟨hC, h⟩ ↦ ⟨by simpa using hC, fun D hD hDC n ↦ ?_⟩,
    fun ⟨hC, h⟩ ↦ ⟨by simpa using hC, fun R hR hCR n ↦ ?_⟩⟩
  · filter_upwards [h (fun n ω ↦ (D n ω)ᶜ) (by simpa using hD)
      (fun k ↦ (hDC k).mono fun _ ↦ compl_subset_compl.2) n] with ω hω
    exact compl_subset_compl.1 hω
  · filter_upwards [h (fun n ω ↦ (R n ω)ᶜ) hR
      (fun k ↦ (hCR k).mono fun _ ↦ compl_subset_comm.1) n] with ω hω
    exact subset_compl_comm.1 hω

/-- **Admissible confidence sequences give admissible tests** [RRLK, Theorem 30]. For an
admissible confidence sequence `C` at level `α`, rejecting `θ` at the times at which `C` misses it
is an admissible level-`α` sequential test of the null `S θ`, for every parameter `θ`. -/
theorem IsAdmissibleConfSeq.isAdmissibleSequentialTest (hC : IsAdmissibleConfSeq C ℱ S α)
    (θ : Θ) :
    IsAdmissibleSequentialTest (fun n ↦ {ω | θ ∉ C n ω}.indicator 1) ℱ (S θ) α := by
  obtain ⟨hC, hCmax⟩ := isAdmissibleConfSeq_iff.1 hC
  refine isAdmissibleSequentialTest_iff.2 ⟨hC.isSequentialTest θ, fun ψ hψ hCψ n ↦ ?_⟩
  -- removing `θ` from `C` where a dominating test `ψ` rejects it keeps a confidence sequence
  set D : ℕ → Ω → Set Θ := fun n ω ↦ {θ' ∈ C n ω | θ' = θ → ψ n ω = 0} with hD_def
  have hD : IsConfSeq D ℱ S α := by
    refine ⟨fun θ' n ↦ ?_, fun θ' P hP ↦ ?_⟩
    · by_cases h : θ' = θ
      · subst h
        simpa [hD_def, ofPred_and, preimage, eq_comm] using
          (hC.measurableSet_mem θ' n).inter (hψ.adapted n (measurableSet_singleton 0))
      · simpa [hD_def, h] using hC.measurableSet_mem θ' n
    by_cases h : θ' = θ
    · -- `D` misses `θ` only where `ψ` rejects, since `ψ` rejects wherever `C` misses `θ`
      subst h
      refine (hψ.measure_exists_eq_one_le P hP).trans' (measure_mono_ae ?_)
      filter_upwards [hψ.ae_exists_eq_one_le hP hCψ] with ω hω ⟨k, hk⟩
      rcases hψ.eq_zero_or_eq_one k ω with h0 | h1
      · simp only [hD_def, h0, mem_ofPred_eq, forall_const, and_true] at hk
        exact hω ⟨k, by simp [hk]⟩
      · exact ⟨k, h1⟩
    · simpa [hD_def, h] using hC.measure_exists_notMem_le θ' P hP
  -- by admissibility, `C n ⊆ D n` quasi-surely, so `ψ` does not reject `θ` where `C n` has it
  have hCD := (hCmax D hD (fun _ ↦ .of_forall fun _ _ h ↦ h.1) n).filter_mono
    (quasiSure_mono (subset_iUnion S θ))
  filter_upwards [hCD] with ω hω
  by_cases hθ : θ ∈ C n ω
  · simp [(hω hθ).2 rfl]
  · rcases hψ.eq_zero_or_eq_one n ω with h | h <;> simp [hθ, h]

/-- **Admissible tests give admissible confidence sequences** [RRLK, Theorem 30]. For countably
many parameters, and nulls `S θ` such that every event of time `n` that is null under every law
of `S θ` is null under every law of the model `⋃ θ, S θ`, the parameters not rejected by a family
of admissible level-`α` sequential tests `φ θ` of the nulls `S θ` form an admissible confidence
sequence at level `α`. -/
theorem isAdmissibleConfSeq_of_isAdmissibleSequentialTest [Countable Θ]
    {φ : Θ → ℕ → Ω → ℝ≥0∞} (hφ : ∀ θ, IsAdmissibleSequentialTest (φ θ) ℱ (S θ) α)
    (hS : ∀ θ θ' n s, MeasurableSet[ℱ n] s → (∀ P ∈ S θ, P s = 0) → ∀ P ∈ S θ', P s = 0) :
    IsAdmissibleConfSeq (fun n ω ↦ {θ | φ θ n ω = 0}) ℱ S α := by
  have hφ' θ := isAdmissibleSequentialTest_iff.1 (hφ θ)
  refine isAdmissibleConfSeq_iff.2 ⟨isConfSeq_of_isSequentialTest fun θ ↦ (hφ' θ).1,
    fun D hD hDC n ↦ ?_⟩
  -- for each parameter, the test read off `D` dominates `φ θ`, so it equals `φ θ` under `S θ`,
  -- and the event that they differ at time `n` is null under the whole model
  have hθ (θ : Θ) : ∀ᶠ ω in quasiSure (⋃ θ, S θ), φ θ n ω = 0 → θ ∈ D n ω := by
    have hdom (k : ℕ) : φ θ k ≤ᶠ[quasiSure (S θ)] {ω | θ ∉ D k ω}.indicator 1 := by
      filter_upwards [(hDC k).filter_mono (quasiSure_mono (subset_iUnion S θ))] with ω hω
      rcases (hφ' θ).1.eq_zero_or_eq_one k ω with h0 | h1
      · simp [h0]
      · have hθD : θ ∉ D k ω := fun h ↦ by simpa [h1] using hω h
        simp [h1, hθD]
    have h := (hφ' θ).2 _ (hD.isSequentialTest θ) hdom n
    have hs : MeasurableSet[ℱ n] {ω | φ θ n ω = 0 ∧ θ ∉ D n ω} :=
      ((hφ' θ).1.adapted n (measurableSet_singleton 0)).inter (hD.measurableSet_notMem θ n)
    have hs0 : ∀ P ∈ S θ, P {ω | φ θ n ω = 0 ∧ θ ∉ D n ω} = 0 := fun P hP ↦
      measure_eq_zero_iff_ae_notMem.2 ((ae_of_eventually_quasiSure h hP).mono
        fun ω hω ⟨h0, hθD⟩ ↦ by simp [hθD, h0] at hω)
    refine eventually_quasiSure_iff.2 fun P hP ↦ ?_
    obtain ⟨θ', hP'⟩ := mem_iUnion.1 hP
    exact (measure_eq_zero_iff_ae_notMem.1 (hS θ θ' n _ hs hs0 P hP')).mono
      fun ω hω h0 ↦ by_contra fun hθD ↦ hω ⟨h0, hθD⟩
  filter_upwards [eventually_countable_forall.2 hθ] with ω hω θ hθC
  exact hω θ hθC

/-- **The admissibility of confidence sequences is that of their tests** [RRLK, Theorem 30]. For
countably many parameters, and nulls `S θ` such that every event of time `n` that is null under
every law of `S θ` is null under every law of the model `⋃ θ, S θ`, a family of random sets is an
admissible confidence sequence at level `α` exactly when rejecting each `θ` at the times at which
it misses `θ` is an admissible level-`α` sequential test of the null `S θ`. -/
theorem isAdmissibleConfSeq_iff_forall_isAdmissibleSequentialTest [Countable Θ]
    (hS : ∀ θ θ' n s, MeasurableSet[ℱ n] s → (∀ P ∈ S θ, P s = 0) → ∀ P ∈ S θ', P s = 0) :
    IsAdmissibleConfSeq C ℱ S α ↔
      ∀ θ, IsAdmissibleSequentialTest (fun n ↦ {ω | θ ∉ C n ω}.indicator 1) ℱ (S θ) α := by
  refine ⟨fun hC θ ↦ hC.isAdmissibleSequentialTest θ, fun h ↦ ?_⟩
  -- the parameters not rejected by the tests `𝟙{θ ∉ C n}` are those of `C n`
  have h_eq : (fun n ω ↦ {θ | {ω | θ ∉ C n ω}.indicator (1 : Ω → ℝ≥0∞) ω = 0}) = C := by
    ext n ω θ
    by_cases hθ : θ ∈ C n ω <;> simp [hθ]
  have hC := isAdmissibleConfSeq_of_isAdmissibleSequentialTest h hS
  rwa [h_eq] at hC

/-- **Admissible confidence sequences from test supermartingales** [RRLK, Theorem 30 (2)]. For
countably many parameters, nulls `S θ` such that every event of time `n` that is null under every
law of `S θ` is null under every law of the model `⋃ θ, S θ`, a level `α ≠ ∞`, and test
supermartingales `M θ` for the nulls `S θ` such that every event of time `n` on which `M θ` has
stayed below `α⁻¹`, charged by a law of `S θ`, is charged by a law of `S θ` under which `M θ`
reaches `α⁻¹` with probability exactly `α`,
the parameters `θ` for which `M θ` has stayed below `α⁻¹` up to time `n` form an admissible
confidence sequence at level `α`. -/
theorem isAdmissibleConfSeq_of_isTestSupermartingale [Countable Θ] {M : Θ → ℕ → Ω → ℝ≥0∞}
    (hM : ∀ θ, IsTestSupermartingale (M θ) ℱ (S θ)) (hα : α ≠ ∞)
    (hMα : ∀ θ n s, MeasurableSet[ℱ n] s → s ⊆ {ω | ∀ k ≤ n, M θ k ω < α⁻¹} →
      (∃ P ∈ S θ, P s ≠ 0) → ∃ P ∈ S θ, P s ≠ 0 ∧ P {ω | ∃ n, α⁻¹ ≤ M θ n ω} = α)
    (hS : ∀ θ θ' n s, MeasurableSet[ℱ n] s → (∀ P ∈ S θ, P s = 0) → ∀ P ∈ S θ', P s = 0) :
    IsAdmissibleConfSeq (fun n ω ↦ {θ | ∀ k ≤ n, M θ k ω < α⁻¹}) ℱ S α := by
  -- the parameters not rejected by the tests of the test supermartingales
  have h_eq : (fun n ω ↦ {θ | {ω | ∃ k ≤ n, α⁻¹ ≤ M θ k ω}.indicator (1 : Ω → ℝ≥0∞) ω = 0}) =
      fun n ω ↦ {θ | ∀ k ≤ n, M θ k ω < α⁻¹} := by
    ext n ω θ
    simp [indicator_apply_eq_zero]
  have hC := isAdmissibleConfSeq_of_isAdmissibleSequentialTest
    (fun θ ↦ (hM θ).isAdmissibleSequentialTest hα (hMα θ)) hS
  rwa [h_eq] at hC

end ProbabilityTheory
