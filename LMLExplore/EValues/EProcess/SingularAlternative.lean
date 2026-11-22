/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.EValues.EProcess.ProductNumeraire
import LMLExplore.EValues.Numeraire
import LMLExplore.EValues.TestSupermartingale.IID
import LMLExplore.Probability.Process.StoppedValue

/-!
# Optimality at every stopping time against an alternative with a singular part

For a simple i.i.d. null, the law `P₁ ^ ℕ` of independent observations with law `P₁`, and the
i.i.d. alternative `Q₁ ^ ℕ`, the likelihood ratio process is optimal at every stopping time that is
finite everywhere when `Q₁ ≪ P₁` (`ProbabilityTheory.isNumeraireAt_prod_rnDeriv`). This file shows
that absolute continuity cannot be dropped [EVR26, Note 40, Proposition 6 (2)]: when `Q₁` has a
singular part with respect to `P₁` and its absolutely continuous part charges both a set `A` and its
complement, no process is optimal both at time `1` and at the stopping time equal to `1` if the
first observation is in `A` and to `2` otherwise. The product of the one-step numeraires is still
optimal at every fixed time (`ProbabilityTheory.isNumeraireAt_prod_const`): the obstruction is that
the mass of the part of the alternative that the null does not exclude, which normalizes the
numeraire, depends on the stopping time.

Both hypotheses are needed. For the null of one Dirac mass `δ_z`, the process equal to `1` while
the observations agree with `z` and to `∞` afterwards is optimal at every stopping time against
every finite alternative (`ProbabilityTheory.isNumeraireAt_dirac`); for `z = 0` on `Bool` and
Bernoulli observations, the alternative has a singular part but no set splits its absolutely
continuous part, a Dirac mass. And when `Q₁` is singular to `P₁`, the process equal to `∞` from the
first observation in a `P₁`-null set carrying `Q₁` on, and to `1` before, is optimal at every
stopping time (`ProbabilityTheory.isNumeraireAt_ite_top_of_mutuallySingular`).

## Main statements

* `ProbabilityTheory.isEProcess_ite_top`: the process equal to `∞` from the first observation in a
  set `N` on, and to `1` before, is an e-process for every null of measures of mass at most one
  under which no observation falls in `N`.
* `ProbabilityTheory.not_isNumeraireAt_one_and_ite`: for an alternative with a singular part and a
  set `A` that splits its absolutely continuous part, no process is optimal both at time `1` and at
  the stopping time `1` on `{ω 0 ∈ A}` and `2` elsewhere [EVR26, Note 40, Proposition 6 (2)].
  `ProbabilityTheory.not_isNumeraireAt_one_and_ite_of_null` is the same statement with a null set
  carrying the singular part.
* `ProbabilityTheory.not_exists_forall_isNumeraireAt`: hence no process is optimal at every
  stopping time that is finite everywhere.
* `ProbabilityTheory.isNumeraireAt_dirac`,
  `ProbabilityTheory.isNumeraireAt_ite_top_of_mutuallySingular`: the two hypotheses of
  `not_isNumeraireAt_one_and_ite` cannot be dropped.

## Implementation notes

The statements and the proofs are adapted from the file `notes/lean-wip/StoppedPaths.lean` and
its auxiliary file `notes/lean-wip/StoppedPathsAux.lean` (commit `c6c6ba8`) of the paper project
`RemyDegenne/evalues_research` (Apache 2.0), with stopping times valued in `WithTop ℕ`, the
filtration `Filtration.piLT`, and the e-process `ProbabilityTheory.isEProcess_ite_top` stated for
every null under which the observations avoid `N`.

## References

* [EVR26] *Answers to open questions in e-values and anytime-valid inference*, the notes and the
  Lean library `EValuesResearch` of github.com/RemyDegenne/evalues_research, 2026, Note 40,
  Proposition 6, and the examples of its referee after it.
-/

public section

open MeasureTheory Set Finset Filtration
open scoped ENNReal

namespace ProbabilityTheory

variable {𝓧 : Type*} {m𝓧 : MeasurableSpace 𝓧} {τ : (ℕ → 𝓧) → WithTop ℕ}

/-! ### The process that becomes infinite on an excluded event -/

/-- **The process that becomes infinite on an excluded event.** For a measurable set `N` and a null
`S` of measures of mass at most one under which, almost surely, no observation falls in `N`, the
process equal to `∞` from the first observation in `N` on, and to `1` before, is an e-process for
`Filtration.piLT`. An instance is the i.i.d. law of `P₁` for a `P₁`-null set `N`. -/
theorem isEProcess_ite_top {S : Set (Measure (ℕ → 𝓧))} (hS : ∀ P ∈ S, P univ ≤ 1) {N : Set 𝓧}
    [DecidablePred (· ∈ N)] (hN : MeasurableSet N) (hSN : ∀ P ∈ S, ∀ᵐ ω ∂P, ∀ i, ω i ∉ N) :
    IsEProcess (fun n ω ↦ if ∃ i < n, ω i ∈ N then ∞ else 1) piLT S := by
  -- the event that one of the first `n` observations is in `N` is known at time `n`
  have h_set (n : ℕ) : MeasurableSet[piLT n] {ω : ℕ → 𝓧 | ∃ i < n, ω i ∈ N} := by
    have h_eq : {ω : ℕ → 𝓧 | ∃ i < n, ω i ∈ N} =
        ⋃ i ∈ range n, (fun ω : ℕ → 𝓧 ↦ ω i) ⁻¹' N := by
      ext ω
      simp
    rw [h_eq]
    exact Finset.measurableSet_biUnion _ fun i hi ↦ measurable_piLT_apply (mem_range.1 hi) hN
  refine (isEProcess_one piLT hS).congr
    (fun n ↦ Measurable.ite (h_set n) measurable_const measurable_const)
    fun n ↦ eventuallyEq_quasiSure_iff.2 fun P hP ↦ ?_
  filter_upwards [hSN P hP] with ω hω
  exact (ite_eq_right fun ⟨i, _, hi⟩ ↦ hω i hi).symm

/-! ### No e-process is optimal at every stopping time -/

/-- The time equal to `1` if the first observation is in a measurable set `A` and to `2` otherwise
is a stopping time of `Filtration.piLT`. -/
private lemma isStoppingTime_ite_mem {A : Set 𝓧} [DecidablePred (· ∈ A)] (hA : MeasurableSet A) :
    IsStoppingTime piLT fun ω : ℕ → 𝓧 ↦ if ω 0 ∈ A then (1 : WithTop ℕ) else 2 := by
  convert isStoppingTime_piLT_comp_initSeg (k := 1) (T := fun x ↦ if x 0 ∈ A then 1 else 2)
    (Measurable.ite (measurable_pi_apply 0 hA) measurable_const measurable_const)
    (fun x ↦ by split_ifs <;> omega) using 2 with ω
  simp only [initSeg_apply, Fin.val_zero]
  split_ifs <;> rfl

/-- **No e-process is optimal at every stopping time, with a null set carrying the singular
part.** Let `P₁` and `Q₁` be probability measures and `N` a measurable `P₁`-null set off which
`Q₁` is absolutely continuous with respect to `P₁`, with `Q₁ N ≠ 0`, and let `A` be a measurable set
such that `Q₁` charges `A \ N` and `Aᶜ \ N`. For the simple null of the i.i.d. law of `P₁` and the
i.i.d. law of `Q₁`, no process is optimal both at time `1` and at the stopping time equal to `1` if
the first observation is in `A` and to `2` otherwise. -/
theorem not_isNumeraireAt_one_and_ite_of_null {P₁ Q₁ : Measure 𝓧} [IsProbabilityMeasure P₁]
    [IsProbabilityMeasure Q₁] {N : Set 𝓧} (hN : MeasurableSet N) (hPN : P₁ N = 0)
    (hQN : Q₁.restrict Nᶜ ≪ P₁) (hQN0 : Q₁ N ≠ 0) {A : Set 𝓧} [DecidablePred (· ∈ A)]
    (hA : MeasurableSet A) (hA₁ : Q₁ (A \ N) ≠ 0) (hA₂ : Q₁ (Aᶜ \ N) ≠ 0)
    (E : ℕ → (ℕ → 𝓧) → ℝ≥0∞) :
    ¬ (IsNumeraireAt E piLT {Measure.infinitePi fun _ ↦ P₁} (Measure.infinitePi fun _ ↦ Q₁)
        (fun _ ↦ 1) ∧
      IsNumeraireAt E piLT {Measure.infinitePi fun _ ↦ P₁} (Measure.infinitePi fun _ ↦ Q₁)
        (fun ω ↦ if ω 0 ∈ A then 1 else 2)) := by
  -- Plan. By optimality at time `1` and uniqueness, `E 1 ω = X (ω 0)` for the one-step
  -- numeraire `X`, which is `∞` on `N`; by optimality at `τ`, `E` is `∞` at `τ` once an
  -- observation is in `N`. With `α = Q₁ (A \ N)`, `β = Q₁ (Aᶜ \ N)` and `c = α + β = Q₁ Nᶜ < 1`,
  -- the competitor `F` equal at time `1` to the normalized numeraire of the first observation on
  -- `A` gives `c ≤ ∫⁻ F_τ / E_τ ∂Q ≤ Q {0 < E_τ < ∞} ≤ α + β * c`, which forces `c = 1`.
  classical
  rintro ⟨h1, h2⟩
  set P := Measure.infinitePi fun _ : ℕ ↦ P₁ with hP_def
  set Q := Measure.infinitePi fun _ : ℕ ↦ Q₁ with hQ_def
  -- the stopping time, as the cast of a time with values in `ℕ`
  set τ : (ℕ → 𝓧) → ℕ := fun ω ↦ if ω 0 ∈ A then 1 else 2 with hτ_def
  have hτ_cast : (fun ω : ℕ → 𝓧 ↦ if ω 0 ∈ A then (1 : WithTop ℕ) else 2) =
      fun ω ↦ (τ ω : WithTop ℕ) := by
    funext ω
    simp only [hτ_def]
    split_ifs <;> rfl
  have h1_cast : (fun _ : ℕ → 𝓧 ↦ (1 : WithTop ℕ)) = fun _ ↦ ((1 : ℕ) : WithTop ℕ) := by
    simp
  rw [hτ_cast] at h2
  rw [h1_cast] at h1
  have hτ_mem (ω : ℕ → 𝓧) (h : ω 0 ∈ A) : τ ω = 1 := ite_eq_left h
  have hτ_notMem (ω : ℕ → 𝓧) (h : ω 0 ∉ A) : τ ω = 2 := ite_eq_right h
  have hτ : IsStoppingTime piLT fun ω ↦ (τ ω : WithTop ℕ) := hτ_cast ▸ isStoppingTime_ite_mem hA
  have h_eval0 : Measurable[piLT 1] fun ω : ℕ → 𝓧 ↦ ω 0 := measurable_piLT_apply zero_lt_one
  -- the one-step numeraire, and the masses
  set X : 𝓧 → ℝ≥0∞ := N.piecewise (fun _ ↦ ∞) ((Q₁[|Nᶜ]).rnDeriv P₁) with hX_def
  have hX : IsNumeraire X {P₁} Q₁ := isNumeraire_piecewise_rnDeriv_cond hN hPN hQN
  have hX_supp : ∀ᵐ x ∂Q₁, x ∈ X.fsupport ↔ x ∉ N :=
    hX.ae_mem_fsupport_iff_notMem prob_le_one hN hQN fun x hx ↦ piecewise_eq_of_mem _ _ _ hx
  set α := Q₁ (A \ N) with hα
  set β := Q₁ (Aᶜ \ N) with hβ
  set c := Q₁ Nᶜ with hc
  have hα_top : α ≠ ∞ := measure_ne_top _ _
  have hβ_top : β ≠ ∞ := measure_ne_top _ _
  have hαβ : α + β = c := by
    rw [hα, hβ, hc, ← measure_union
      (Set.disjoint_left.2 fun x (h1 : x ∈ A \ N) (h2 : x ∈ Aᶜ \ N) ↦ h2.1 h1.1)
      (hA.compl.diff hN)]
    congr 1
    ext x
    simp only [Set.mem_union, Set.mem_sdiff, Set.mem_compl_iff]
    tauto
  have hc_ne_one : c ≠ 1 := fun h ↦ hQN0 ((prob_compl_eq_one_iff hN).1 h)
  have hc0 : c ≠ 0 := fun h ↦ hA₁ (add_eq_zero.1 (hαβ.trans h)).1
  set a := ∫⁻ x in A, X x ∂P₁ with ha
  have ha_eq : a = c⁻¹ * α := setLIntegral_piecewise_rnDeriv_cond hN hPN hQN A
  have ha0 : a ≠ 0 := by
    rw [ha_eq]
    exact mul_ne_zero (ENNReal.inv_ne_zero.2 (measure_ne_top _ _)) hA₁
  have ha_top : a ≠ ∞ := by
    rw [ha_eq]
    exact ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 hc0) hα_top
  have hv_meas : MeasurableSet (A ∩ X.fsupport) := hA.inter hX.measurable.measurable_fsupport
  have hv : Q ((fun ω : ℕ → 𝓧 ↦ ω 0) ⁻¹' (A ∩ X.fsupport)) = α := by
    rw [(measurePreserving_eval_infinitePi (fun _ : ℕ ↦ Q₁) 0).measure_preimage
      hv_meas.nullMeasurableSet]
    refine measure_congr (Filter.eventuallyEqSet_iff.2 ?_)
    filter_upwards [hX_supp] with x hx
    exact ⟨fun h ↦ ⟨h.1, hx.1 h.2⟩, fun h ↦ ⟨h.1, hx.2 h.2⟩⟩
  -- at time `1`, the process is the one-step numeraire of the first observation
  have hS₁ : ∀ _ : ℕ, ∀ μ ∈ ({P₁} : Set (Measure 𝓧)), IsProbabilityMeasure μ := by
    rintro _ _ rfl
    infer_instance
  have hE' : IsEProcess (fun n ω ↦ ∏ i ∈ range n, X (ω i)) piLT {P} := by
    have h := (hX.isEVar.isEProcess_prod_piLT (hS₁ 0)).anti_set (iidNull_singleton P₁).ge
    convert h using 3 with n ω
    exact (Fin.prod_univ_eq_prod_range (fun i ↦ X (ω i)) n).symm
  have h1' := isNumeraireAt_prod_const (S₁ := fun _ ↦ {P₁}) (Q₁ := fun _ ↦ Q₁) (X := fun _ ↦ X)
    hS₁ (fun _ ↦ singleton_nonempty P₁) (fun _ ↦ hX)
    (fun R hR ↦ by rw [funext hR]; rfl) hE' 1
  have hE1 : ∀ᵐ ω ∂Q, E 1 ω = X (ω 0) := by
    filter_upwards [h1.ae_eq h1' measurable_const] with ω hω
    simpa only [stoppedValue_natCast (τ := fun _ ↦ 1), prod_range_one] using hω
  -- at `τ`, the process is infinite as soon as an observation is in `N`
  have hE_top : ∀ᵐ ω ∂Q, (∃ i < τ ω, ω i ∈ N) → E (τ ω) ω = ∞ := by
    have hPN' : ∀ μ ∈ ({P} : Set (Measure (ℕ → 𝓧))), ∀ᵐ ω ∂μ, ∀ i, ω i ∉ N := by
      rintro _ rfl
      exact Measure.ae_forall_apply_infinitePi _ fun _ ↦ measure_eq_zero_iff_ae_notMem.1 hPN
    filter_upwards [h2.ae_eq_top_of_eq_top (isEProcess_ite_top (by simp) hN hPN')
      hτ.measurable'] with ω hω h
    simp only [stoppedValue_natCast] at hω
    exact hω (ite_eq_left h)
  -- the competitor: the numeraire of the first observation on `A`, normalized, at time `1`
  set W : (ℕ → 𝓧) → ℝ≥0∞ := fun ω ↦ A.indicator X (ω 0) / a with hW
  have hW_int : ∫⁻ ω, W ω ∂P = 1 := by
    rw [hW, (measurePreserving_eval_infinitePi (fun _ : ℕ ↦ P₁) 0).lintegral_comp
      (f := fun x ↦ A.indicator X x / a) ((hX.measurable.indicator hA).div_const a)]
    simp_rw [div_eq_mul_inv]
    rw [lintegral_mul_const _ (hX.measurable.indicator hA), lintegral_indicator hA, ← ha,
      ENNReal.mul_inv_cancel ha0 ha_top]
  set F : ℕ → (ℕ → 𝓧) → ℝ≥0∞ := fun n ω ↦ if n = 1 then W ω else 0 with hF_def
  have hF_ad : Adapted piLT F := fun n ↦ by
    by_cases hn : n = 1
    · have hFn : F n = W := funext fun ω ↦ by simp [hF_def, hn]
      rw [hFn, hn]
      exact ((hX.measurable.indicator hA).comp h_eval0).div_const a
    · have hFn : F n = fun _ ↦ 0 := funext fun ω ↦ by simp [hF_def, hn]
      rw [hFn]
      exact measurable_const
  have hF : IsEProcess F piLT {P} := by
    refine IsEProcess.of_lintegral_le_one hF_ad fun ρ _ _ _ μ hμ ↦ ?_
    obtain rfl : μ = P := hμ
    refine (lintegral_mono fun ω ↦ ?_).trans hW_int.le
    simp only [stoppedValue, hF_def]
    split_ifs
    exacts [le_rfl, zero_le]
  have h_ineq := ((isNumeraireAt_iff hτ.measurable').1 h2).2 F hF
  simp only [stoppedValue_natCast] at h_ineq
  -- the left-hand side of the inequality at `τ` is at least `c`
  have h_lower : c ≤ ∫⁻ ω, F (τ ω) ω / E (τ ω) ω ∂Q := by
    calc c
    _ = a⁻¹ * α := by
      rw [ha_eq, ENNReal.mul_inv (.inr hα_top) (.inr hA₁), inv_inv, mul_assoc,
        ENNReal.inv_mul_cancel hA₁ hα_top, mul_one]
    _ = ∫⁻ ω, ((fun ω : ℕ → 𝓧 ↦ ω 0) ⁻¹' (A ∩ X.fsupport)).indicator (fun _ ↦ a⁻¹) ω ∂Q := by
      rw [lintegral_indicator_const (measurable_pi_apply 0 hv_meas), hv]
    _ ≤ ∫⁻ ω, F (τ ω) ω / E (τ ω) ω ∂Q := by
      refine lintegral_mono_ae ?_
      filter_upwards [hE1] with ω hω
      by_cases hmem : ω 0 ∈ A ∩ X.fsupport
      · rw [indicator_of_mem (show ω ∈ (fun ω : ℕ → 𝓧 ↦ ω 0) ⁻¹' (A ∩ X.fsupport) from hmem),
          hτ_mem ω hmem.1, hω]
        simp only [hF_def, ite_true, hW, indicator_of_mem hmem.1]
        rw [div_eq_mul_inv, div_eq_mul_inv, mul_right_comm,
          ENNReal.mul_inv_cancel hmem.2.2 hmem.2.1, one_mul]
      · rw [indicator_of_notMem (show ω ∉ (fun ω : ℕ → 𝓧 ↦ ω 0) ⁻¹' (A ∩ X.fsupport)
          from hmem)]
        exact zero_le
  -- the right-hand side is at most `α + β * c`
  have h_upper : Q (fun ω ↦ E (τ ω) ω).fsupport ≤ α + β * c := by
    calc Q (fun ω ↦ E (τ ω) ω).fsupport
    _ ≤ Q ((fun ω : ℕ → 𝓧 ↦ ω 0) ⁻¹' (A ∩ X.fsupport) ∪
        {ω | ω 0 ∈ Aᶜ \ N ∧ ω 1 ∈ Nᶜ}) := by
      refine measure_mono_ae ?_
      filter_upwards [hE1, hE_top] with ω hω1 hω_top hω
      by_cases hA0 : ω 0 ∈ A
      · left
        have hω' : E (τ ω) ω ≠ ∞ ∧ E (τ ω) ω ≠ 0 := hω
        rw [hτ_mem ω hA0, hω1] at hω'
        exact ⟨hA0, hω'⟩
      · right
        have h_no : ¬ ∃ i < τ ω, ω i ∈ N := fun h ↦ hω.1 (hω_top h)
        rw [hτ_notMem ω hA0] at h_no
        exact ⟨⟨hA0, fun h ↦ h_no ⟨0, by norm_num, h⟩⟩, fun h ↦ h_no ⟨1, by norm_num, h⟩⟩
    _ ≤ Q ((fun ω : ℕ → 𝓧 ↦ ω 0) ⁻¹' (A ∩ X.fsupport)) +
        Q {ω | ω 0 ∈ Aᶜ \ N ∧ ω 1 ∈ Nᶜ} := measure_union_le _ _
    _ = α + β * c := by
      rw [hv]
      congr 1
      have h_pi : {ω : ℕ → 𝓧 | ω 0 ∈ Aᶜ \ N ∧ ω 1 ∈ Nᶜ} =
          (({0, 1} : Finset ℕ) : Set ℕ).pi fun i ↦ if i = 0 then Aᶜ \ N else Nᶜ := by
        ext ω
        simp
      rw [h_pi, Measure.infinitePi_pi _ fun i _ ↦ by
        split_ifs
        exacts [hA.compl.diff hN, hN.compl], prod_pair zero_ne_one,
        ite_eq_left (rfl : (0 : ℕ) = 0), ite_eq_right (one_ne_zero : (1 : ℕ) ≠ 0)]
  -- so `c ≤ α + β * c` with `c = α + β < 1` and `β > 0`: a contradiction
  have h_le : α + β ≤ α + β * c := hαβ ▸ h_lower.trans (h_ineq.trans h_upper)
  have h_le' : β * 1 ≤ β * c := by
    rw [mul_one]
    exact (ENNReal.add_le_add_iff_left hα_top).1 h_le
  exact hc_ne_one (le_antisymm prob_le_one ((ENNReal.mul_le_mul_iff_right hA₂ hβ_top).1 h_le'))

/-- **No e-process is optimal at every stopping time when the alternative charges, in part, an
event that the null excludes** [EVR26, Note 40, Proposition 6 (2)]. Let `P₁` and `Q₁` be
probability measures such that `Q₁` is not absolutely continuous with respect to `P₁`, and let `A`
be a measurable set such that the absolutely continuous part of `Q₁` charges `A` and its
complement. Then, for the simple null of the i.i.d. law of `P₁` and the i.i.d. law of `Q₁`, no
process is optimal both at time `1` and at the stopping time equal to `1` if the first observation
is in `A` and to `2` otherwise. -/
theorem not_isNumeraireAt_one_and_ite {P₁ Q₁ : Measure 𝓧} [IsProbabilityMeasure P₁]
    [IsProbabilityMeasure Q₁] (hQP : Q₁.singularPart P₁ ≠ 0) {A : Set 𝓧} [DecidablePred (· ∈ A)]
    (hA : MeasurableSet A) (hA₁ : P₁.withDensity (Q₁.rnDeriv P₁) A ≠ 0)
    (hA₂ : P₁.withDensity (Q₁.rnDeriv P₁) Aᶜ ≠ 0) (E : ℕ → (ℕ → 𝓧) → ℝ≥0∞) :
    ¬ (IsNumeraireAt E piLT {Measure.infinitePi fun _ ↦ P₁} (Measure.infinitePi fun _ ↦ Q₁)
        (fun _ ↦ 1) ∧
      IsNumeraireAt E piLT {Measure.infinitePi fun _ ↦ P₁} (Measure.infinitePi fun _ ↦ Q₁)
        (fun ω ↦ if ω 0 ∈ A then 1 else 2)) := by
  -- a `P₁`-null set that carries the singular part of `Q₁`
  set ν := Q₁.singularPart P₁ with hν
  set D := P₁.withDensity (Q₁.rnDeriv P₁) with hD
  have h_sing : ν ⟂ₘ P₁ := Measure.mutuallySingular_singularPart Q₁ P₁
  have hQ_apply (s : Set 𝓧) : Q₁ s = ν s + D s := by
    rw [← add_apply, ← Measure.haveLebesgueDecomposition_add Q₁ P₁]
  set N := h_sing.nullSetᶜ with hN_def
  have hN : MeasurableSet N := h_sing.measurableSet_nullSet.compl
  have hPN : P₁ N = 0 := h_sing.measure_compl_nullSet
  have hνN : ν Nᶜ = 0 := by
    rw [hN_def, compl_compl]
    exact h_sing.measure_nullSet
  have hDN : D N = 0 := withDensity_absolutelyContinuous _ _ hPN
  have hQN : Q₁.restrict Nᶜ ≪ P₁ := by
    refine Measure.AbsolutelyContinuous.mk fun s hs hPs ↦ ?_
    rw [Measure.restrict_apply hs, hQ_apply, measure_mono_null Set.inter_subset_right hνN,
      measure_mono_null Set.inter_subset_left (withDensity_absolutelyContinuous _ _ hPs),
      add_zero]
  have hQ_diff (B : Set 𝓧) : Q₁ (B \ N) = D B := by
    rw [hQ_apply, measure_mono_null (show B \ N ⊆ Nᶜ from fun x hx ↦ hx.2) hνN, zero_add,
      measure_sdiff_null hDN]
  have hQN0 : Q₁ N ≠ 0 := by
    rw [hQ_apply, hDN, add_zero]
    intro h
    refine hQP (Measure.measure_univ_eq_zero.1 ?_)
    rw [← Set.union_compl_self N]
    exact measure_union_null h hνN
  exact not_isNumeraireAt_one_and_ite_of_null hN hPN hQN hQN0 hA
    (by rwa [hQ_diff]) (by rwa [hQ_diff]) E

/-- **No e-process is optimal at every stopping time** [EVR26, Note 40, Proposition 6 (2)]. For
probability measures `P₁` and `Q₁` such that `Q₁` is not absolutely continuous with respect to
`P₁`, and whose absolutely continuous part charges a measurable set `A` and its complement, no
process is optimal at every stopping time that is finite everywhere, for the simple null of the
i.i.d. law of `P₁` against the i.i.d. law of `Q₁`. -/
theorem not_exists_forall_isNumeraireAt {P₁ Q₁ : Measure 𝓧} [IsProbabilityMeasure P₁]
    [IsProbabilityMeasure Q₁] (hQP : Q₁.singularPart P₁ ≠ 0) {A : Set 𝓧} (hA : MeasurableSet A)
    (hA₁ : P₁.withDensity (Q₁.rnDeriv P₁) A ≠ 0) (hA₂ : P₁.withDensity (Q₁.rnDeriv P₁) Aᶜ ≠ 0) :
    ¬ ∃ E : ℕ → (ℕ → 𝓧) → ℝ≥0∞, ∀ τ : (ℕ → 𝓧) → WithTop ℕ, IsStoppingTime piLT τ →
      (∀ ω, τ ω ≠ ⊤) →
        IsNumeraireAt E piLT {Measure.infinitePi fun _ ↦ P₁} (Measure.infinitePi fun _ ↦ Q₁) τ := by
  classical
  rintro ⟨E, hE⟩
  refine not_isNumeraireAt_one_and_ite hQP hA hA₁ hA₂ E
    ⟨hE _ (by simpa using isStoppingTime_natCast 1) fun _ ↦ WithTop.one_ne_top,
      hE _ (isStoppingTime_ite_mem hA) fun ω ↦ ?_⟩
  split_ifs
  exacts [WithTop.one_ne_top, WithTop.natCast_ne_top 2]

/-! ### The hypotheses cannot be dropped -/

/-- **A simple null of one Dirac mass has an e-process that is optimal at every stopping time**
(example of the referee of [EVR26, Note 40], after Proposition 6). For the null of the Dirac mass
at a sequence `z`, the process equal to `1` while the observations agree with `z` and to `∞`
afterwards is optimal at every stopping time that is finite everywhere, against every finite
measure. For `𝓧 = Bool`, `z = 0` and the i.i.d. law of a Bernoulli law with parameter in `(0, 1)`,
the alternative charges events that the null excludes, but no set splits its absolutely continuous
part, a Dirac mass: the last hypotheses of `not_isNumeraireAt_one_and_ite` cannot be dropped. -/
theorem isNumeraireAt_dirac [MeasurableSingletonClass 𝓧] [DecidableEq 𝓧] (z : ℕ → 𝓧)
    (Q : Measure (ℕ → 𝓧)) [IsFiniteMeasure Q] (hτ : IsStoppingTime piLT τ)
    (hτ_top : ∀ ω, τ ω ≠ ⊤) :
    IsNumeraireAt (fun n ω ↦ if ∀ i < n, ω i = z i then 1 else ∞) piLT {Measure.dirac z} Q τ := by
  set E : ℕ → (ℕ → 𝓧) → ℝ≥0∞ := fun n ω ↦ if ∀ i < n, ω i = z i then 1 else ∞ with hE_def
  have h_set (n : ℕ) : MeasurableSet[piLT n] {ω : ℕ → 𝓧 | ∀ i < n, ω i = z i} := by
    have h_eq : {ω : ℕ → 𝓧 | ∀ i < n, ω i = z i} =
        ⋂ i ∈ range n, (fun ω : ℕ → 𝓧 ↦ ω i) ⁻¹' {z i} := by
      ext ω
      simp
    rw [h_eq]
    exact Finset.measurableSet_biInter _ fun i hi ↦
      measurable_piLT_apply (mem_range.1 hi) (measurableSet_singleton _)
  have hE_ad : Adapted piLT E := fun n ↦ Measurable.ite (h_set n) measurable_const measurable_const
  have hE : IsEProcess E piLT {Measure.dirac z} := by
    refine IsEProcess.of_lintegral_le_one hE_ad fun ρ hρ _ _ P hP ↦ ?_
    obtain rfl : P = Measure.dirac z := hP
    rw [lintegral_dirac' z (measurable_stoppedValue_of_countable (fun _ ↦ hE_ad.measurable)
      hρ.measurable')]
    exact (ite_eq_left fun _ _ ↦ rfl).le
  obtain ⟨τ, rfl⟩ := WithTop.exists_eq_natCast_of_forall_ne_top hτ_top
  rw [isNumeraireAt_iff hτ.measurable']
  refine ⟨hE, fun F hF ↦ ?_⟩
  simp only [stoppedValue_natCast]
  have hF_le : F (τ z) z ≤ 1 := by
    have h := hF.lintegral_le_one hτ hτ_top (P := Measure.dirac z) rfl
    rwa [lintegral_dirac' z (hF.measurable_stoppedValue hτ), stoppedValue_natCast] at h
  have hEτ_meas : Measurable fun ω ↦ E (τ ω) ω := by
    have h := hE.measurable_stoppedValue hτ
    rwa [stoppedValue_natCast] at h
  rw [← lintegral_indicator_one hEτ_meas.measurable_fsupport]
  refine lintegral_mono fun ω ↦ ?_
  by_cases hω : ∀ i < τ ω, ω i = z i
  · -- the path agrees with `z` up to `τ`: then `τ`, and `F` at `τ`, are those of `z`
    have hEω : E (τ ω) ω = 1 := ite_eq_left hω
    have hτz : τ z = τ ω := Nat.cast_inj.1 (hτ.eq_of_forall_lt rfl hω)
    have hFz : F (τ ω) ω = F (τ ω) z := (hF.adapted (τ ω)).dependsOn_of_piLT hω
    have h_supp : ω ∈ (fun ω ↦ E (τ ω) ω).fsupport := by
      simp [Function.fsupport, hEω]
    rw [indicator_of_mem h_supp, hEω, div_one, hFz, ← hτz]
    exact hF_le
  · have hEω : E (τ ω) ω = ∞ := ite_eq_right hω
    rw [hEω, ENNReal.div_top]
    exact zero_le

/-- **For a singular alternative, an e-process is optimal at every stopping time** (example of
the referee of [EVR26, Note 40], after Proposition 6). Let `P₁` and `Q₁` be probability measures
and `N` a measurable `P₁`-null set that carries `Q₁`. For the simple null of the i.i.d. law of
`P₁` and the i.i.d. law of `Q₁`, the process equal to `∞` from the first observation in `N` on,
and to `1` before, is optimal at every stopping time that is finite everywhere: the hypothesis of
`not_isNumeraireAt_one_and_ite` that the absolutely continuous part of `Q₁` is not zero cannot be
dropped. -/
theorem isNumeraireAt_ite_top_of_mutuallySingular {P₁ Q₁ : Measure 𝓧} [IsProbabilityMeasure P₁]
    [IsProbabilityMeasure Q₁] {N : Set 𝓧} [DecidablePred (· ∈ N)] (hN : MeasurableSet N)
    (hPN : P₁ N = 0) (hQN : Q₁ Nᶜ = 0) (hτ : IsStoppingTime piLT τ) (hτ_top : ∀ ω, τ ω ≠ ⊤) :
    IsNumeraireAt (fun n ω ↦ if ∃ i < n, ω i ∈ N then ∞ else 1) piLT
      {Measure.infinitePi fun _ ↦ P₁} (Measure.infinitePi fun _ ↦ Q₁) τ := by
  set E : ℕ → (ℕ → 𝓧) → ℝ≥0∞ := fun n ω ↦ if ∃ i < n, ω i ∈ N then ∞ else 1 with hE_def
  -- under the alternative every observation is in `N`
  have hQ_ae : ∀ᵐ ω ∂Measure.infinitePi fun _ : ℕ ↦ Q₁, ∀ i, ω i ∈ N :=
    Measure.ae_forall_apply_infinitePi (fun _ ↦ Q₁) fun _ ↦ by
      filter_upwards [measure_eq_zero_iff_ae_notMem.1 hQN] with x hx using not_not.1 hx
  have hPN' : ∀ μ ∈ ({Measure.infinitePi fun _ ↦ P₁} : Set (Measure (ℕ → 𝓧))),
      ∀ᵐ ω ∂μ, ∀ i, ω i ∉ N := by
    rintro _ rfl
    exact Measure.ae_forall_apply_infinitePi _ fun _ ↦ measure_eq_zero_iff_ae_notMem.1 hPN
  obtain ⟨τ, rfl⟩ := WithTop.exists_eq_natCast_of_forall_ne_top hτ_top
  rw [isNumeraireAt_iff hτ.measurable']
  refine ⟨isEProcess_ite_top (by simp) hN hPN', fun F hF ↦ ?_⟩
  simp only [stoppedValue_natCast]
  by_cases h0 : ∃ ω, τ ω = 0
  · -- time `0` has seen nothing: the stopping time is `0` everywhere and `F 0` is a constant
    obtain ⟨ω₀, hω₀⟩ := h0
    have hτ0 (ω : ℕ → 𝓧) : τ ω = 0 :=
      Nat.cast_inj.1 (hτ.eq_of_forall_lt (by rw [hω₀]) fun i hi ↦ absurd hi (Nat.not_lt_zero i))
    have hF0 (ω : ℕ → 𝓧) : F 0 ω = F 0 ω₀ :=
      (hF.adapted 0).dependsOn_of_piLT fun i hi ↦ absurd hi (Nat.not_lt_zero i)
    have hc : F 0 ω₀ ≤ 1 := by
      have h := (hF.isEVar 0).lintegral_le_one (μ := Measure.infinitePi fun _ ↦ P₁) rfl
      simp_rw [hF0] at h
      simpa using h
    have h_supp : (fun ω ↦ E (τ ω) ω).fsupport = Set.univ := by
      ext ω
      simp [Function.fsupport, hτ0, hE_def]
    rw [h_supp, measure_univ]
    calc ∫⁻ ω, F (τ ω) ω / E (τ ω) ω ∂Measure.infinitePi fun _ ↦ Q₁
    _ = ∫⁻ _, F 0 ω₀ ∂Measure.infinitePi fun _ ↦ Q₁ :=
      lintegral_congr fun ω ↦ by simp [hτ0, hF0 ω, hE_def]
    _ = F 0 ω₀ := by simp
    _ ≤ 1 := hc
  · -- the stopping time is positive: the process is infinite at it, almost surely
    refine le_of_eq_of_le (lintegral_eq_zero_of_ae_eq_zero ?_) zero_le
    filter_upwards [hQ_ae] with ω hω
    have hEω : E (τ ω) ω = ∞ :=
      ite_eq_left ⟨0, Nat.pos_of_ne_zero fun h ↦ h0 ⟨ω, h⟩, hω 0⟩
    simp [hEω]

end ProbabilityTheory
