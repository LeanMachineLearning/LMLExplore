/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Probability.Independence.Basic
public import Statlib.EValues.EVariable
import LMLExplore.EValues.Merging
import LMLExplore.MeasureTheory.Constructions.Pi
import LMLExplore.MeasureTheory.Integral.Pi
import LMLExplore.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.Algebra.BigOperators.Fin

/-!
# Merging functions for independent e-values

A merging function for independent e-values indexed by a finite type `ι` is a measurable
`F : (ι → ℝ≥0∞) → ℝ≥0∞` with `∫⁻ e, F e ∂Measure.pi μ ≤ 1` for all probability measures `μ i` on
`ℝ≥0∞` with expectation at most `1`. The law of e-variables that are independent under a
probability measure is such a product, so `F` turns e-variables that are independent under every
member of the null into an e-variable, and this characterizes merging functions for independent
e-values (`ProbabilityTheory.isIEMerging_iff_forall_isEVar`). No monotonicity is assumed. Such a
function is precise when its integral is `1` against every product of laws with expectation `1`.
As for e-merging functions, the values at infinite arguments are irrelevant
(`ProbabilityTheory.IsIEMerging.of_le`), so domination is a statement about finite arguments.

For two e-values, the generalized martingale merging functions of [VW24, Section 6] are, in a
normal form, the mixtures `w₁ * M₁ + w₂ * M₂`, with an initial capital `w₁ + w₂ ≤ 1`, of
martingale merging functions that read the two e-values in either order. Reading `e 0` first, a
fraction `a₁ ∈ [0, 1]` of the capital is bet on `e 0`, then a fraction `g₁ (e 0) ∈ [0, 1]` on
`e 1`, which gives `M₁ e = ((1 - a₁) + a₁ * e 0) * ((1 - g₁ (e 0)) + g₁ (e 0) * e 1)`; `M₂` reads
`e 1` first, with bets `a₂` and `g₂ (e 1)`. Vovk and Wang ask whether every increasing merging
function for independent e-values is dominated by such a function, and whether every precise one
is such a function [VW24, Section 7]. Both answers are negative, already for two e-values, and
the precise merging functions do not dominate every increasing one either
[EVR26, Notes 08 and 17]:

* the increasing function `𝟙{1 ≤ e 0} + 𝟙{e 0 < 1, 2 ≤ e 1} + 𝟙{2 ≤ e 0, 1 ≤ e 1}` is a merging
  function for independent e-values that no generalized martingale merging function dominates;
* the function `1 + 𝟙{e 0 < 2} * (e 1 - 1) + 𝟙{1 ≤ e 1} * (e 0 - 1)` is a precise merging function
  for independent e-values that no generalized martingale merging function dominates;
* an increasing step function on the cells of `{0, 1/2, 2, 3}` is a merging function for
  independent e-values that no precise one dominates.

## Main definitions

* `ProbabilityTheory.IsIEMerging F`: `F` is a merging function for independent e-values.
* `ProbabilityTheory.IsPreciseIEMerging F`: `F` is a precise merging function for independent
  e-values.

## Main statements

* `ProbabilityTheory.IsIEMerging.isEVar_comp`: a merging function for independent e-values of
  e-variables that are independent under every member of the null is an e-variable, and
  `ProbabilityTheory.isIEMerging_iff_forall_isEVar` characterizes these functions by this property.
* `ProbabilityTheory.IsIEMerging.of_le`: a measurable function dominated on finite arguments by a
  merging function for independent e-values is one.
* `ProbabilityTheory.exists_isIEMerging_monotone_not_le_mixture_martingale`: an increasing merging
  function for two independent e-values that no generalized martingale merging function
  dominates.
* `ProbabilityTheory.exists_isPreciseIEMerging_not_le_mixture_martingale`: a precise merging
  function for two independent e-values that no generalized martingale merging function
  dominates.
* `ProbabilityTheory.exists_isIEMerging_monotone_not_le_isPreciseIEMerging`: an increasing merging
  function for two independent e-values that no precise one dominates.

## Implementation notes

The three functions and the proofs that no generalized martingale or precise merging function
dominates them are adapted from `EValuesResearch/Results/IEMerging.lean` (commit `9d33415`) in the
paper project `RemyDegenne/evalues_research` (same author). There, the mixtures are parametrized
by an initial capital `c` and a weight `β` instead of the weights `w₁ = c * β` and
`w₂ = c * (1 - β)`, the bets `g₁`, `g₂` are assumed measurable, and domination is required at
every argument rather than at finite arguments.

The generalized martingale merging functions of two e-values are written out in the statements,
in the normal form above. The bets `g₁`, `g₂` are not assumed measurable, and the mixtures are
not assumed to be merging functions, which only strengthens the statements.

Integrals against `Measure.pi` over `Fin 2` are computed as iterated integrals. The validity of a
step function of two e-values reduces, by Markov's inequality on its steps, to a real inequality
on the masses of the steps. That no generalized martingale merging function dominates the first
two functions follows from the values of both functions at a few points of `{0, 1/2, 1, 2}²`.
That no precise function dominates the third uses the definition of precise only: a precise
function integrates to `1` against four products of two-point laws with mean `1` on
`{0, 1/2, 2, 3}`, and a signed combination of these four products is a law on eight points
against which the third function integrates to `47 / 43`.

## References

* [VW24] V. Vovk and R. Wang, *Merging sequential e-values via martingales*, Electron. J.
  Statist. 18 (2024), arXiv:2007.06382v3: Section 2 (merging functions for independent e-values),
  Section 6 (generalized martingale merging functions), Section 7 (the questions answered here).
* [EVR26] *Answers to open questions in e-values and anytime-valid inference*, notes and the Lean
  library `EValuesResearch` of github.com/RemyDegenne/evalues_research, 2026: Note 08 (the first
  two functions) and Note 17 (the third function).
-/

public section

open MeasureTheory
open scoped ENNReal NNReal

namespace ProbabilityTheory

universe u

/-! ### Merging functions for independent e-values -/

section Definition

variable {ι : Type*} [Fintype ι] {F G : (ι → ℝ≥0∞) → ℝ≥0∞}

/-- A **merging function for independent e-values** indexed by `ι` [VW24, Section 2]: a
measurable `F : (ι → ℝ≥0∞) → ℝ≥0∞` with `∫⁻ e, F e ∂Measure.pi μ ≤ 1` for all probability
measures `μ i` on `ℝ≥0∞` with expectation at most `1`. It is not required to be monotone. -/
structure IsIEMerging (F : (ι → ℝ≥0∞) → ℝ≥0∞) : Prop where
  measurable : Measurable F
  lintegral_le_one : ∀ (μ : ι → Measure ℝ≥0∞) [∀ i, IsProbabilityMeasure (μ i)],
    (∀ i, ∫⁻ x, x ∂μ i ≤ 1) → ∫⁻ e, F e ∂Measure.pi μ ≤ 1

/-- A **precise merging function for independent e-values** [VW24, Section 7]: a merging function
for independent e-values whose integral against `Measure.pi μ` is `1` for all probability measures
`μ i` on `ℝ≥0∞` with expectation `1`. -/
structure IsPreciseIEMerging (F : (ι → ℝ≥0∞) → ℝ≥0∞) : Prop extends IsIEMerging F where
  lintegral_eq_one : ∀ (μ : ι → Measure ℝ≥0∞) [∀ i, IsProbabilityMeasure (μ i)],
    (∀ i, ∫⁻ x, x ∂μ i = 1) → ∫⁻ e, F e ∂Measure.pi μ = 1

/-- A measurable function dominated on finite arguments by a merging function for independent
e-values is one: the values at infinite arguments are irrelevant, since the coordinates are
almost surely finite under a product of laws with finite expectations. -/
theorem IsIEMerging.of_le (hG : IsIEMerging G) (hF : Measurable F)
    (hle : ∀ e : ι → ℝ≥0, F (fun i ↦ e i) ≤ G (fun i ↦ e i)) : IsIEMerging F := by
  refine ⟨hF, fun μ _ hμ ↦ (lintegral_mono_ae (ae_le_of_forall_nnreal_le ?_ hle)).trans
    (hG.lintegral_le_one μ hμ)⟩
  exact Filter.eventually_all.2 fun i ↦
    Measure.tendsto_eval_ae_ae.eventually <| (ae_lt_top measurable_id'
      ((hμ i).trans_lt ENNReal.one_lt_top).ne).mono fun _ h ↦ h.ne

/-- A merging function for independent e-values, applied to e-variables that are independent under
every member of the null, is an e-variable. -/
theorem IsIEMerging.isEVar_comp {Ω : Type*} {mΩ : MeasurableSpace Ω} {S : Set (Measure Ω)}
    (hF : IsIEMerging F) (hS : ∀ P ∈ S, IsProbabilityMeasure P) {E : ι → Ω → ℝ≥0∞}
    (hE : ∀ i, IsEVar (E i) S) (hindep : ∀ P ∈ S, iIndepFun E P) :
    IsEVar (fun ω ↦ F fun i ↦ E i ω) S := by
  have hm : Measurable fun ω i ↦ E i ω := measurable_pi_iff.2 fun i ↦ (hE i).measurable
  refine IsEVar.of_lintegral_le_one hS (hF.measurable.comp hm) fun P hP ↦ ?_
  have := hS P hP
  rw [← lintegral_map hF.measurable hm,
    (hindep P hP).map_fun_eq_pi_map fun i ↦ (hE i).measurable.aemeasurable]
  refine hF.lintegral_le_one _ fun i ↦ ?_
  rw [lintegral_map measurable_id' (hE i).measurable]
  simpa using (hE i).lintegral_le_measure_univ P hP

/-- A function of e-values is a merging function for independent e-values exactly when it turns
e-variables that are independent under every member of the null into an e-variable, for every
null hypothesis of probability measures on every measurable space in the universe of `ι`. The
forward direction holds on measurable spaces in any universe
(`ProbabilityTheory.IsIEMerging.isEVar_comp`). -/
theorem isIEMerging_iff_forall_isEVar {ι : Type u} [Fintype ι] {F : (ι → ℝ≥0∞) → ℝ≥0∞} :
    IsIEMerging F ↔ ∀ (Ω : Type u) [MeasurableSpace Ω] (S : Set (Measure Ω)),
      (∀ P ∈ S, IsProbabilityMeasure P) → ∀ E : ι → Ω → ℝ≥0∞, (∀ i, IsEVar (E i) S) →
        (∀ P ∈ S, iIndepFun E P) → IsEVar (fun ω ↦ F fun i ↦ E i ω) S := by
  refine ⟨fun hF Ω _ S hS E hE hindep ↦ hF.isEVar_comp hS hE hindep, fun h ↦ ?_⟩
  -- the products of laws with expectation at most `1`, and the coordinates
  set S : Set (Measure (ι → ℝ≥0∞)) := {P | ∃ μ : ι → Measure ℝ≥0∞,
    (∀ i, IsProbabilityMeasure (μ i)) ∧ (∀ i, ∫⁻ x, x ∂μ i ≤ 1) ∧ P = Measure.pi μ}
  have hS : ∀ P ∈ S, IsProbabilityMeasure P := by
    rintro _ ⟨μ, hμ, -, rfl⟩
    infer_instance
  have hF := h (ι → ℝ≥0∞) S hS (fun i e ↦ e i)
    (fun i ↦ IsEVar.of_lintegral_le_one hS (measurable_pi_apply i) fun P ↦ by
      rintro ⟨μ, hμ, hmean, rfl⟩
      rw [(measurePreserving_eval μ i).lintegral_comp measurable_id']
      exact hmean i)
    (by
      rintro _ ⟨μ, hμ, -, rfl⟩
      exact iIndepFun_pi (X := fun _ x ↦ x) fun _ ↦ aemeasurable_id')
  refine ⟨hF.measurable, fun μ _ hμ ↦ ?_⟩
  simpa using hF.lintegral_le_measure_univ (Measure.pi μ) ⟨μ, inferInstance, hμ, rfl⟩

end Definition

/-! ### Step functions of two e-values -/

section FinTwo

/-- A step function `f (φ (e 0)) (φ (e 1))` of two e-values, constant on the fibres of a map `φ`
to `Fin n`, is a merging function for independent e-values as soon as a real inequality holds on
the masses `P i`, `Q j` of the fibres. These masses add up to `1`, and a lower bound
`γ (φ x) ≤ x` on the identity turns the constraint on the expectation into
`∑ i, γ i * P i ≤ 1` (Markov's inequality on the steps). -/
private lemma isIEMerging_of_step {n : ℕ} {φ : ℝ≥0∞ → Fin n} (hφ : Measurable φ)
    {γ : Fin n → ℝ≥0∞} (hγ : ∀ x, γ (φ x) ≤ x) {f : Fin n → Fin n → ℝ≥0∞} (hf : ∀ i j, f i j ≠ ∞)
    (h : ∀ P Q : Fin n → ℝ, (∀ i, 0 ≤ P i) → ∑ i, P i = 1 → ∑ i, (γ i).toReal * P i ≤ 1 →
      (∀ j, 0 ≤ Q j) → ∑ j, Q j = 1 → ∑ j, (γ j).toReal * Q j ≤ 1 →
      ∑ i, ∑ j, (f i j).toReal * P i * Q j ≤ 1) :
    IsIEMerging fun e : Fin 2 → ℝ≥0∞ ↦ f (φ (e 0)) (φ (e 1)) := by
  refine ⟨measurable_pi_comp_of_finite (φ := fun _ ↦ φ) (fun _ ↦ hφ) fun k ↦ f (k 0) (k 1),
    fun μ _ hmean ↦ ?_⟩
  have hmass : ∀ k, (∀ i, 0 ≤ (μ k (φ ⁻¹' {i})).toReal) ∧ ∑ i, (μ k (φ ⁻¹' {i})).toReal = 1 ∧
      ∑ i, (γ i).toReal * (μ k (φ ⁻¹' {i})).toReal ≤ 1 := by
    intro k
    refine ⟨fun i ↦ ENNReal.toReal_nonneg, ?_, ?_⟩
    · rw [← ENNReal.toReal_sum (fun i _ ↦ measure_ne_top _ _),
        sum_measure_preimage_singleton _ fun i _ ↦ hφ (measurableSet_singleton i)]
      simp
    · have hle : ∑ i, γ i * μ k (φ ⁻¹' {i}) ≤ 1 := by
        rw [← lintegral_comp_eq_sum_measure_preimage_singleton hφ.aemeasurable]
        exact (lintegral_mono hγ).trans (hmean k)
      have hterm : ∀ i, γ i * μ k (φ ⁻¹' {i}) ≠ ∞ := fun i ↦ ne_top_of_le_ne_top
        ENNReal.one_ne_top ((Finset.single_le_sum (fun j _ ↦ zero_le) (Finset.mem_univ i)).trans
          hle)
      have := ENNReal.toReal_mono ENNReal.one_ne_top hle
      rw [ENNReal.toReal_sum (fun i _ ↦ hterm i), ENNReal.toReal_one] at this
      simpa only [ENNReal.toReal_mul] using this
  have hterm : ∀ i j, f i j * μ 0 (φ ⁻¹' {i}) * μ 1 (φ ⁻¹' {j}) ≠ ∞ := fun i j ↦ by
    have := hf i j
    finiteness
  have hint : ∫⁻ e, f (φ (e 0)) (φ (e 1)) ∂Measure.pi μ =
      ∑ i, ∑ j, f i j * μ 0 (φ ⁻¹' {i}) * μ 1 (φ ⁻¹' {j}) := by
    rw [lintegral_pi_comp_eq_sum μ (φ := fun _ ↦ φ) (fun _ ↦ hφ) fun k ↦ f (k 0) (k 1),
      ← (finTwoArrowEquiv _).symm.sum_comp, Fintype.sum_prod_type]
    simp [Fin.prod_univ_two, mul_assoc]
  rw [hint,
    ← ENNReal.ofReal_toReal (ENNReal.sum_ne_top.2 fun i _ ↦ ENNReal.sum_ne_top.2 fun j _ ↦
      hterm i j), ENNReal.ofReal_le_one,
    ENNReal.toReal_sum fun i _ ↦ ENNReal.sum_ne_top.2 fun j _ ↦ hterm i j]
  simp_rw [ENNReal.toReal_sum fun j _ ↦ hterm _ j, ENNReal.toReal_mul]
  exact h _ _ (hmass 0).1 (hmass 0).2.1 (hmass 0).2.2 (hmass 1).1 (hmass 1).2.1 (hmass 1).2.2

/-- Domination on finite arguments, read at two finite arguments. -/
private lemma le_of_forall_nnreal {F G : (Fin 2 → ℝ≥0∞) → ℝ≥0∞}
    (hle : ∀ e : Fin 2 → ℝ≥0, F (fun i ↦ e i) ≤ G (fun i ↦ e i)) {x y : ℝ≥0∞} (hx : x ≠ ∞)
    (hy : y ≠ ∞) : F ![x, y] ≤ G ![x, y] := by
  have h : (fun i ↦ ((![x.toNNReal, y.toNNReal] : Fin 2 → ℝ≥0) i : ℝ≥0∞)) = ![x, y] := by
    ext i
    fin_cases i <;> simp [hx, hy]
  rw [← h]
  exact hle _

/-! ### Generalized martingale merging functions of two e-values -/

/-- The generalized martingale merging function of two e-values with weights `w₁`, `w₂` on the
two reading orders, first bets `a₁`, `a₂` and second bets `g₁`, `g₂`. -/
private noncomputable def mixMartingale (w₁ w₂ a₁ a₂ : ℝ≥0∞) (g₁ g₂ : ℝ≥0∞ → ℝ≥0∞)
    (e : Fin 2 → ℝ≥0∞) : ℝ≥0∞ :=
  w₁ * ((1 - a₁ + a₁ * e 0) * (1 - g₁ (e 0) + g₁ (e 0) * e 1)) +
    w₂ * ((1 - a₂ + a₂ * e 1) * (1 - g₂ (e 1) + g₂ (e 1) * e 0))

/-- If a generalized martingale merging function of two e-values dominates `F` on finite
arguments, then `F` is finite at finite arguments, and its real value there is at most the
defining formula, with real weights and bets in `[0, 1]`. -/
private lemma exists_toReal_le_of_le_mixMartingale {F : (Fin 2 → ℝ≥0∞) → ℝ≥0∞}
    {w₁ w₂ a₁ a₂ : ℝ≥0∞} {g₁ g₂ : ℝ≥0∞ → ℝ≥0∞} (hw : w₁ + w₂ ≤ 1) (ha₁ : a₁ ≤ 1)
    (ha₂ : a₂ ≤ 1) (hg₁ : ∀ x, g₁ x ≤ 1) (hg₂ : ∀ x, g₂ x ≤ 1)
    (hle : ∀ e : Fin 2 → ℝ≥0, F (fun i ↦ e i) ≤ mixMartingale w₁ w₂ a₁ a₂ g₁ g₂ fun i ↦ e i) :
    ∃ (w₁ w₂ a₁ a₂ : ℝ) (g₁ g₂ : ℝ≥0∞ → ℝ), 0 ≤ w₁ ∧ 0 ≤ w₂ ∧ w₁ + w₂ ≤ 1 ∧ 0 ≤ a₁ ∧ a₁ ≤ 1 ∧
      0 ≤ a₂ ∧ a₂ ≤ 1 ∧ (∀ x, 0 ≤ g₁ x ∧ g₁ x ≤ 1) ∧ (∀ x, 0 ≤ g₂ x ∧ g₂ x ≤ 1) ∧
      ∀ x y : ℝ≥0∞, x ≠ ∞ → y ≠ ∞ → F ![x, y] ≠ ∞ ∧ (F ![x, y]).toReal ≤
        w₁ * ((1 - a₁ + a₁ * x.toReal) * (1 - g₁ x + g₁ x * y.toReal)) +
          w₂ * ((1 - a₂ + a₂ * y.toReal) * (1 - g₂ y + g₂ y * x.toReal)) := by
  have hsub : ∀ a : ℝ≥0∞, a ≤ 1 → (1 - a).toReal = 1 - a.toReal := fun a ha ↦ by
    rw [ENNReal.toReal_sub_of_le ha ENNReal.one_ne_top, ENNReal.toReal_one]
  have hle1 : ∀ a : ℝ≥0∞, a ≤ 1 → a.toReal ≤ 1 := fun a ha ↦ by
    simpa using ENNReal.toReal_mono ENNReal.one_ne_top ha
  have htop : ∀ a : ℝ≥0∞, a ≤ 1 → a ≠ ∞ := fun a ha ↦ ne_top_of_le_ne_top ENNReal.one_ne_top ha
  have hw₁ : w₁ ≤ 1 := le_self_add.trans hw
  have hw₂ : w₂ ≤ 1 := le_add_self.trans hw
  refine ⟨w₁.toReal, w₂.toReal, a₁.toReal, a₂.toReal, fun x ↦ (g₁ x).toReal,
    fun x ↦ (g₂ x).toReal, ENNReal.toReal_nonneg, ENNReal.toReal_nonneg, ?_,
    ENNReal.toReal_nonneg, hle1 a₁ ha₁, ENNReal.toReal_nonneg, hle1 a₂ ha₂,
    fun x ↦ ⟨ENNReal.toReal_nonneg, hle1 _ (hg₁ x)⟩,
    fun x ↦ ⟨ENNReal.toReal_nonneg, hle1 _ (hg₂ x)⟩, fun x y hx hy ↦ ?_⟩
  · rw [← ENNReal.toReal_add (htop _ hw₁) (htop _ hw₂)]
    exact hle1 _ hw
  have := htop _ hw₁
  have := htop _ hw₂
  have := htop a₁ ha₁
  have := htop a₂ ha₂
  have := htop _ (hg₁ x)
  have := htop _ (hg₂ y)
  have hH : mixMartingale w₁ w₂ a₁ a₂ g₁ g₂ ![x, y] ≠ ∞ := by
    simp only [mixMartingale, Matrix.cons_val_zero, Matrix.cons_val_one]
    finiteness
  have hFH := le_of_forall_nnreal hle hx hy
  refine ⟨ne_top_of_le_ne_top hH hFH, (ENNReal.toReal_mono hH hFH).trans_eq ?_⟩
  simp only [mixMartingale, Matrix.cons_val_zero, Matrix.cons_val_one]
  simp (disch := finiteness) only [ENNReal.toReal_mul, ENNReal.toReal_add]
  rw [hsub a₁ ha₁, hsub a₂ ha₂, hsub _ (hg₁ x), hsub _ (hg₂ y)]

/-! ### An increasing merging function that no generalized martingale merging function
dominates -/

/-- The cell of `x` in the partition `[0, 1), [1, 2), [2, ∞]` of `ℝ≥0∞`. -/
private noncomputable def threeCell (x : ℝ≥0∞) : Fin 3 :=
  if x < 1 then 0 else if x < 2 then 1 else 2

/-- The values of `threeCellMerging` on the cells of `threeCell`, rows for the first e-value. -/
private def threeCellTable : Fin 3 → Fin 3 → ℕ := ![![0, 0, 1], ![1, 1, 1], ![1, 2, 2]]

/-- The function `𝟙{1 ≤ e 0} + 𝟙{e 0 < 1, 2 ≤ e 1} + 𝟙{2 ≤ e 0, 1 ≤ e 1}`, written through its
table of values on the cells. -/
private noncomputable def threeCellMerging (e : Fin 2 → ℝ≥0∞) : ℝ≥0∞ :=
  threeCellTable (threeCell (e 0)) (threeCell (e 1))

/-- `threeCell` is measurable. -/
private lemma measurable_threeCell : Measurable threeCell :=
  Measurable.ite measurableSet_Iio measurable_const
    (Measurable.ite measurableSet_Iio measurable_const measurable_const)

/-- `threeCell` is monotone. -/
private lemma monotone_threeCell : Monotone threeCell := by
  intro x y hxy
  unfold threeCell
  split_ifs <;> first | decide | (exfalso; order)

/-- The table `threeCellTable` is monotone in both arguments. -/
private lemma threeCellTable_mono {i i' j j' : Fin 3} (hi : i ≤ i') (hj : j ≤ j') :
    threeCellTable i j ≤ threeCellTable i' j' := by
  revert i i' j j'
  decide

/-- `threeCellMerging` is increasing for the product order. -/
private lemma monotone_threeCellMerging : Monotone threeCellMerging := fun _ _ h ↦
  Nat.cast_le.2 (threeCellTable_mono (monotone_threeCell (h 0)) (monotone_threeCell (h 1)))

/-- The value of `threeCellMerging` at a point whose coordinates lie in the cells `i` and `j`. -/
private lemma threeCellMerging_apply {i j : Fin 3} {x y : ℝ≥0∞} (hx : threeCell x = i)
    (hy : threeCell y = j) : threeCellMerging ![x, y] = threeCellTable i j := by
  simp [threeCellMerging, hx, hy]

/-- `threeCellMerging` is a merging function for independent e-values: with `P i`, `Q j` the
masses of the cells, the constraints on the expectations read `P 2 ≤ P 0` and `Q 2 ≤ Q 0`, and the
integral is `1 - (P 0 * (Q 0 + Q 1) - P 2 * (Q 1 + Q 2))`. -/
private lemma isIEMerging_threeCellMerging : IsIEMerging threeCellMerging := by
  refine isIEMerging_of_step (γ := ![0, 1, 2]) (f := fun i j ↦ (threeCellTable i j : ℝ≥0∞))
    measurable_threeCell ?_ (fun _ _ ↦ ENNReal.natCast_ne_top _) ?_
  · intro x
    unfold threeCell
    split_ifs with h1 h2 <;> simp_all [not_lt]
  · intro P Q hP hPs hPm hQ hQs hQm
    simp [threeCellTable, Fin.sum_univ_three] at hPs hPm hQs hQm ⊢
    nlinarith [mul_nonneg (by linarith : 0 ≤ P 0 - P 2) (add_nonneg (hQ 1) (hQ 2)),
      mul_nonneg (hP 0) (by linarith : 0 ≤ Q 0 - Q 2), congrArg₂ (· * ·) hPs hQs]

/-- There is an increasing merging function for two independent e-values that no generalized
martingale merging function dominates: no mixture `w₁ * M₁ + w₂ * M₂`, `w₁ + w₂ ≤ 1`, of
martingale merging functions `M₁`, `M₂` reading the two e-values in either order, with bets in
`[0, 1]`, is above it at every pair of finite arguments. This answers a question of
[VW24, Section 7], following [EVR26, Note 08]. The function is
`𝟙{1 ≤ e 0} + 𝟙{e 0 < 1, 2 ≤ e 1} + 𝟙{2 ≤ e 0, 1 ≤ e 1}`. -/
theorem exists_isIEMerging_monotone_not_le_mixture_martingale :
    ∃ F : (Fin 2 → ℝ≥0∞) → ℝ≥0∞, IsIEMerging F ∧ Monotone F ∧
      ∀ (w₁ w₂ a₁ a₂ : ℝ≥0∞) (g₁ g₂ : ℝ≥0∞ → ℝ≥0∞), w₁ + w₂ ≤ 1 → a₁ ≤ 1 → a₂ ≤ 1 →
        (∀ x, g₁ x ≤ 1) → (∀ x, g₂ x ≤ 1) →
        ¬ ∀ e : Fin 2 → ℝ≥0, F (fun i ↦ e i) ≤
          w₁ * ((1 - a₁ + a₁ * e 0) * (1 - g₁ (e 0) + g₁ (e 0) * e 1)) +
            w₂ * ((1 - a₂ + a₂ * e 1) * (1 - g₂ (e 1) + g₂ (e 1) * e 0)) := by
  refine ⟨threeCellMerging, isIEMerging_threeCellMerging, monotone_threeCellMerging,
    fun w₁ w₂ a₁ a₂ g₁ g₂ hw ha₁ ha₂ hg₁ hg₂ hle ↦ ?_⟩
  obtain ⟨w₁, w₂, a₁, a₂, g₁, g₂, hw₁, hw₂, hw, ha₁0, ha₁1, ha₂0, ha₂1, hg₁, hg₂, key⟩ :=
    exists_toReal_le_of_le_mixMartingale (F := threeCellMerging) hw ha₁ ha₂ hg₁ hg₂
      (by simpa only [mixMartingale] using hle)
  have h0 : threeCell 0 = 0 := by norm_num [threeCell]
  have h1 : threeCell 1 = 1 := by norm_num [threeCell]
  have h2 : threeCell 2 = 2 := by norm_num [threeCell]
  -- the values at `(2, 1)`, `(1, 0)`, `(0, 2)` and `(2, 2)`
  have h21 := (key 2 1 (by simp) (by simp)).2
  have h10 := (key 1 0 (by simp) (by simp)).2
  have h02 := (key 0 2 (by simp) (by simp)).2
  have h22 := (key 2 2 (by simp) (by simp)).2
  rw [threeCellMerging_apply h2 h1, (by simp [threeCellTable] : threeCellTable 2 1 = 2)] at h21
  rw [threeCellMerging_apply h1 h0, (by simp [threeCellTable] : threeCellTable 1 0 = 1)] at h10
  rw [threeCellMerging_apply h0 h2, (by simp [threeCellTable] : threeCellTable 0 2 = 1)] at h02
  rw [threeCellMerging_apply h2 h2, (by simp [threeCellTable] : threeCellTable 2 2 = 2)] at h22
  simp only [ENNReal.toReal_ofNat, ENNReal.toReal_one, ENNReal.toReal_zero, Nat.cast_ofNat,
    Nat.cast_one] at h21 h10 h02 h22
  have h1a₁ : 0 ≤ 1 - a₁ := by linarith
  -- `H (2, 1) ≥ 2` forces `w₁ + w₂ = 1`, then `w₁ (1 - a₁) = 0`
  obtain rfl : w₂ = 1 - w₁ := by
    nlinarith [mul_nonneg hw₁ h1a₁, mul_nonneg hw₂ (sub_nonneg.2 (hg₂ 1).2)]
  have hA : w₁ * (1 - a₁) = 0 := by
    nlinarith [mul_nonneg hw₁ h1a₁, mul_nonneg hw₂ (sub_nonneg.2 (hg₂ 1).2)]
  -- `H (1, 0) ≥ 1` forces `w₂ a₂ = 0`
  have hB : (1 - w₁) * a₂ = 0 := by
    nlinarith [mul_nonneg hw₁ (hg₁ 1).1, mul_nonneg hw₂ ha₂0]
  have hA' : w₁ * (1 - a₁) * (1 + g₁ 0) = 0 := by rw [hA, zero_mul]
  have hB' : (1 - w₁) * a₂ * (1 - g₂ 2) = 0 := by rw [hB, zero_mul]
  -- `H (0, 2) ≥ 1` forces `w₁ = 0`, hence `a₂ = 0`, and then `H (2, 2) ≤ 1 + g₂ 2 ≤ 1`
  obtain rfl : w₁ = 0 := le_antisymm (by nlinarith [mul_nonneg hw₂ (hg₂ 2).1]) hw₁
  obtain rfl : a₂ = 0 := by simpa using hB
  nlinarith [(hg₂ 2).1]

/-! ### A precise merging function that no generalized martingale merging function dominates -/

/-- The precise merging function `1 + 𝟙{e 0 < 2} * (e 1 - 1) + 𝟙{1 ≤ e 1} * (e 0 - 1)`: it is
`e 1`, `e 0 + e 1 - 1`, `1` and `e 0` on the four quadrants `{e 0 < 2, e 1 < 1}`,
`{e 0 < 2, 1 ≤ e 1}`, `{2 ≤ e 0, e 1 < 1}` and `{2 ≤ e 0, 1 ≤ e 1}`. -/
private noncomputable def kinkMerging (e : Fin 2 → ℝ≥0∞) : ℝ≥0∞ :=
  if e 0 < 2 then (if e 1 < 1 then e 1 else e 0 + e 1 - 1) else (if e 1 < 1 then 1 else e 0)

/-- `kinkMerging` is measurable. -/
private lemma measurable_kinkMerging : Measurable kinkMerging := by
  have h0 := measurable_pi_apply (X := fun _ : Fin 2 ↦ ℝ≥0∞) 0
  have h1 := measurable_pi_apply (X := fun _ : Fin 2 ↦ ℝ≥0∞) 1
  exact Measurable.ite (measurableSet_lt h0 measurable_const)
    (Measurable.ite (measurableSet_lt h1 measurable_const) h1 ((h0.add h1).sub_const 1))
    (Measurable.ite (measurableSet_lt h1 measurable_const) measurable_const h0)

/-- `kinkMerging` written without subtraction, as a sum of products of functions of one
coordinate. -/
private lemma kinkMerging_add (e : Fin 2 → ℝ≥0∞) :
    kinkMerging e + (Set.Iio 2).indicator 1 (e 0) * (Set.Iio 1)ᶜ.indicator 1 (e 1) =
      (Set.Iio 2).indicator 1 (e 0) * e 1 + e 0 * (Set.Iio 1)ᶜ.indicator 1 (e 1) +
        (Set.Iio 2)ᶜ.indicator 1 (e 0) * (Set.Iio 1).indicator 1 (e 1) := by
  rcases lt_or_ge (e 0) 2 with h0 | h0 <;> rcases lt_or_ge (e 1) 1 with h1 | h1
  · simp [kinkMerging, h0, h1]
  · simp [kinkMerging, h0, h1, h1.not_gt, tsub_add_cancel_of_le (h1.trans le_add_self), add_comm]
  · simp [kinkMerging, Set.indicator_apply, h0.not_gt, h1]
  · simp [kinkMerging, Set.indicator_apply, h0.not_gt, h1.not_gt]

/-- The integral of `kinkMerging` against a product of two σ-finite measures, plus a correction
term, in terms of the expectations and of the masses of `[0, 2)` and `[0, 1)`. -/
private lemma lintegral_kinkMerging_add (μ : Fin 2 → Measure ℝ≥0∞) [∀ i, SigmaFinite (μ i)] :
    ∫⁻ e, kinkMerging e ∂Measure.pi μ + μ 0 (Set.Iio 2) * μ 1 (Set.Iio 1)ᶜ =
      μ 0 (Set.Iio 2) * ∫⁻ y, y ∂μ 1 + (∫⁻ x, x ∂μ 0) * μ 1 (Set.Iio 1)ᶜ +
        μ 0 (Set.Iio 2)ᶜ * μ 1 (Set.Iio 1) := by
  have hs : MeasurableSet (Set.Iio (2 : ℝ≥0∞)) := measurableSet_Iio
  have ht : MeasurableSet (Set.Iio (1 : ℝ≥0∞)) := measurableSet_Iio
  have hind : ∀ {s : Set ℝ≥0∞}, MeasurableSet s → Measurable (s.indicator (1 : ℝ≥0∞ → ℝ≥0∞)) :=
    fun hs ↦ measurable_one.indicator hs
  have m₁ := hind hs
  have m₂ := hind ht.compl
  have m₃ := hind hs.compl
  have m₄ := hind ht
  have L : ∫⁻ e, (kinkMerging e + (Set.Iio 2).indicator 1 (e 0) * (Set.Iio 1)ᶜ.indicator 1 (e 1))
      ∂Measure.pi μ = ∫⁻ e, ((Set.Iio 2).indicator 1 (e 0) * e 1 +
        e 0 * (Set.Iio 1)ᶜ.indicator 1 (e 1) +
        (Set.Iio 2)ᶜ.indicator 1 (e 0) * (Set.Iio 1).indicator 1 (e 1)) ∂Measure.pi μ := by
    simp_rw [kinkMerging_add]
  rwa [lintegral_add_left measurable_kinkMerging,
    lintegral_pi_fin_two_mul μ m₁.aemeasurable m₂.aemeasurable,
    lintegral_add_left (by fun_prop), lintegral_add_left (by fun_prop),
    lintegral_pi_fin_two_mul μ m₁.aemeasurable aemeasurable_id',
    lintegral_pi_fin_two_mul μ aemeasurable_id' m₂.aemeasurable,
    lintegral_pi_fin_two_mul μ m₃.aemeasurable m₄.aemeasurable, lintegral_indicator_one hs,
    lintegral_indicator_one ht.compl, lintegral_indicator_one hs.compl,
    lintegral_indicator_one ht] at L

/-- If `A + A' = 1` and `B + B' = 1` in `ℝ≥0∞`, then `A + B + A' * B' = A * B + 1`. -/
private lemma add_add_mul_eq_mul_add_one {A A' B B' : ℝ≥0∞} (hA : A + A' = 1) (hB : B + B' = 1) :
    A + B + A' * B' = A * B + 1 :=
  calc A + B + A' * B' = A * (B + B') + (A + A') * B + A' * B' := by
        rw [hA, hB, mul_one, one_mul]
    _ = A * B + (A + A') * (B + B') := by ring
    _ = A * B + 1 := by rw [hA, hB, one_mul]

/-- `kinkMerging` is a precise merging function for independent e-values: by independence, its
integral is `1 + P(E₀ < 2) * (E[E₁] - 1) + P(1 ≤ E₁) * (E[E₀] - 1)`. -/
private lemma isPreciseIEMerging_kinkMerging : IsPreciseIEMerging kinkMerging := by
  have key : ∀ μ : Fin 2 → Measure ℝ≥0∞, (∀ i, IsProbabilityMeasure (μ i)) →
      μ 0 (Set.Iio 2) + μ 1 (Set.Iio 1)ᶜ + μ 0 (Set.Iio 2)ᶜ * μ 1 (Set.Iio 1) =
        μ 0 (Set.Iio 2) * μ 1 (Set.Iio 1)ᶜ + 1 := fun μ hμ ↦
    add_add_mul_eq_mul_add_one (by rw [measure_add_measure_compl measurableSet_Iio, measure_univ])
      (by rw [add_comm, measure_add_measure_compl measurableSet_Iio, measure_univ])
  refine ⟨⟨measurable_kinkMerging, fun μ hμ hmean ↦ ?_⟩, fun μ hμ hmean ↦ ?_⟩
  · have h := lintegral_kinkMerging_add μ
    rw [← ENNReal.add_le_add_iff_right (by finiteness : μ 0 (Set.Iio 2) * μ 1 (Set.Iio 1)ᶜ ≠ ∞),
      h, add_comm 1, ← key μ hμ]
    gcongr
    · exact mul_le_of_le_one_right zero_le (hmean 1)
    · exact mul_le_of_le_one_left zero_le (hmean 0)
  · have h := lintegral_kinkMerging_add μ
    rw [hmean 0, hmean 1, mul_one, one_mul, key μ hμ, add_comm _ 1] at h
    exact (ENNReal.add_left_inj (by finiteness)).1 h

/-- The values of `kinkMerging` used to show that no generalized martingale merging function
dominates it. -/
private lemma kinkMerging_values : kinkMerging ![1, 1] = 1 ∧ kinkMerging ![2, 1] = 2 ∧
    kinkMerging ![1, 2] = 2 ∧ kinkMerging ![0, 2⁻¹] = 2⁻¹ ∧ kinkMerging ![2, 0] = 1 ∧
    kinkMerging ![0, 2] = 1 ∧ kinkMerging ![2, 2] = 2 := by
  have h₂ : (2 : ℝ≥0∞) - 1 = 1 := ENNReal.sub_eq_of_eq_add_rev ENNReal.one_ne_top (by norm_num)
  have h₃ : (3 : ℝ≥0∞) - 1 = 2 := ENNReal.sub_eq_of_eq_add_rev ENNReal.one_ne_top (by norm_num)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num [kinkMerging, h₂, h₃]

/-- There is a precise merging function for two independent e-values that no generalized
martingale merging function dominates: no mixture `w₁ * M₁ + w₂ * M₂`, `w₁ + w₂ ≤ 1`, of
martingale merging functions `M₁`, `M₂` reading the two e-values in either order, with bets in
`[0, 1]`, is above it at every pair of finite arguments. In particular, not every precise merging
function is a generalized martingale merging function, which answers a question of
[VW24, Section 7], following [EVR26, Note 08]. The function is
`1 + 𝟙{e 0 < 2} * (e 1 - 1) + 𝟙{1 ≤ e 1} * (e 0 - 1)`. -/
theorem exists_isPreciseIEMerging_not_le_mixture_martingale :
    ∃ F : (Fin 2 → ℝ≥0∞) → ℝ≥0∞, IsPreciseIEMerging F ∧
      ∀ (w₁ w₂ a₁ a₂ : ℝ≥0∞) (g₁ g₂ : ℝ≥0∞ → ℝ≥0∞), w₁ + w₂ ≤ 1 → a₁ ≤ 1 → a₂ ≤ 1 →
        (∀ x, g₁ x ≤ 1) → (∀ x, g₂ x ≤ 1) →
        ¬ ∀ e : Fin 2 → ℝ≥0, F (fun i ↦ e i) ≤
          w₁ * ((1 - a₁ + a₁ * e 0) * (1 - g₁ (e 0) + g₁ (e 0) * e 1)) +
            w₂ * ((1 - a₂ + a₂ * e 1) * (1 - g₂ (e 1) + g₂ (e 1) * e 0)) := by
  refine ⟨kinkMerging, isPreciseIEMerging_kinkMerging,
    fun w₁ w₂ a₁ a₂ g₁ g₂ hw ha₁ ha₂ hg₁ hg₂ hle ↦ ?_⟩
  obtain ⟨w₁, w₂, a₁, a₂, g₁, g₂, hw₁, hw₂, hw, ha₁0, ha₁1, ha₂0, ha₂1, hg₁, hg₂, key⟩ :=
    exists_toReal_le_of_le_mixMartingale (F := kinkMerging) hw ha₁ ha₂ hg₁ hg₂
      (by simpa only [mixMartingale] using hle)
  obtain ⟨v11, v21, v12, v0h, v20, v02, v22⟩ := kinkMerging_values
  have k11 := (key 1 1 (by simp) (by simp)).2
  have k21 := (key 2 1 (by simp) (by simp)).2
  have k12 := (key 1 2 (by simp) (by simp)).2
  have k0h := (key 0 2⁻¹ (by simp) (by simp)).2
  have k20 := (key 2 0 (by simp) (by simp)).2
  have k02 := (key 0 2 (by simp) (by simp)).2
  have k22 := (key 2 2 (by simp) (by simp)).2
  rw [v11] at k11
  rw [v21] at k21
  rw [v12] at k12
  rw [v0h] at k0h
  rw [v20] at k20
  rw [v02] at k02
  rw [v22] at k22
  simp only [ENNReal.toReal_ofNat, ENNReal.toReal_one, ENNReal.toReal_zero, ENNReal.toReal_inv]
    at k11 k21 k12 k0h k20 k02 k22
  -- `H (1, 1) ≥ 1` forces `w₁ + w₂ = 1`
  obtain rfl : w₂ = 1 - w₁ := by linarith
  -- `w₁ = 0`: `H (1, 2) ≥ 2` forces `a₂ = 1`, and then `H (2, 0) = 0`
  rcases hw₁.eq_or_lt with rfl | hwpos
  · obtain rfl : a₂ = 1 := le_antisymm ha₂1 (by linarith)
    linarith
  -- `w₁ = 1`: `H (2, 1) ≥ 2` forces `a₁ = 1`, and then `H (0, 1/2) = 0`
  have hw₁1 : w₁ ≤ 1 := by linarith
  rcases hw₁1.eq_or_lt with rfl | hwlt
  · obtain rfl : a₁ = 1 := le_antisymm ha₁1 (by linarith)
    linarith
  -- `0 < w₁ < 1`: `a₁ = a₂ = 1`; `H (2, 0) ≥ 1` and the product of the laws with mean one
  -- `(δ₀ + δ₂)/2` and `(2 δ_{1/2} + δ₂)/3`, against which `H` integrates to at most `1`, force
  -- `H (2, 1/2) ≤ 1`, while `H (2, 1/2) ≥ 1 + (1 - w₁) / 2`
  obtain rfl : a₁ = 1 :=
    le_antisymm ha₁1 (by nlinarith [mul_nonneg hw₂ (sub_nonneg.2 (hg₂ 1).2)])
  obtain rfl : a₂ = 1 :=
    le_antisymm ha₂1 (by nlinarith [mul_nonneg hw₁ (sub_nonneg.2 (hg₁ 1).2)])
  nlinarith [mul_nonneg hw₁ (hg₁ 2).1,
    mul_pos (sub_pos.2 hwlt) (by linarith [(hg₂ 2⁻¹).1] : (0 : ℝ) < 1 + g₂ 2⁻¹)]

/-! ### An increasing merging function that no precise merging function dominates -/

/-- A linear function `r` of the laws `P` on `{0, 1/2, 2, 3}` with expectation at most `1` is at
most `1` as soon as it is at most `1` at the six extreme laws `δ₀`, `δ_{1/2}`, `(δ₀ + δ₂)/2`,
`(2δ₀ + δ₃)/3`, `(2δ_{1/2} + δ₂)/3` and `(4δ_{1/2} + δ₃)/5`. The proof splits the triangular prism
of these laws into three simplices, according to the position of `P₁` relative to `4 P₃` and to
`2 P₂ + 4 P₃`. -/
private lemma sum_mul_le_one_of_extreme {P₀ P₁ P₂ P₃ r₀ r₁ r₂ r₃ : ℝ} (h₀ : 0 ≤ P₀)
    (h₁ : 0 ≤ P₁) (h₂ : 0 ≤ P₂) (h₃ : 0 ≤ P₃) (hs : P₀ + P₁ + P₂ + P₃ = 1)
    (hm : P₁ / 2 + 2 * P₂ + 3 * P₃ ≤ 1) (hr₀ : r₀ ≤ 1) (hr₁ : r₁ ≤ 1) (hA : r₀ + r₂ ≤ 2)
    (hB : 2 * r₀ + r₃ ≤ 3) (hC : 2 * r₁ + r₂ ≤ 3) (hD : 4 * r₁ + r₃ ≤ 5) :
    r₀ * P₀ + r₁ * P₁ + r₂ * P₂ + r₃ * P₃ ≤ 1 := by
  obtain rfl : P₀ = 1 - P₁ - P₂ - P₃ := by linarith
  rcases le_total P₁ (4 * P₃) with h | h
  · nlinarith [mul_nonneg (sub_nonneg.2 hm) (sub_nonneg.2 hr₀), mul_nonneg h₂ (sub_nonneg.2 hA),
      mul_nonneg (sub_nonneg.2 h) (sub_nonneg.2 hB), mul_nonneg h₁ (sub_nonneg.2 hD)]
  rcases le_total P₁ (2 * P₂ + 4 * P₃) with h' | h'
  · nlinarith [mul_nonneg (sub_nonneg.2 hm) (sub_nonneg.2 hr₀), mul_nonneg (sub_nonneg.2 h)
      (sub_nonneg.2 hC), mul_nonneg (sub_nonneg.2 h') (sub_nonneg.2 hA),
      mul_nonneg h₃ (sub_nonneg.2 hD)]
  · nlinarith [mul_nonneg h₀ (sub_nonneg.2 hr₀), mul_nonneg (sub_nonneg.2 h') (sub_nonneg.2 hr₁),
      mul_nonneg h₂ (sub_nonneg.2 hC), mul_nonneg h₃ (sub_nonneg.2 hD)]

/-- The cell of `x` in the partition `[0, 1/2), [1/2, 2), [2, 3), [3, ∞]` of `ℝ≥0∞`: the index
of the largest element of `{0, 1/2, 2, 3}` not exceeding `x`. -/
private noncomputable def fourCell (x : ℝ≥0∞) : Fin 4 :=
  if x < 2⁻¹ then 0 else if x < 2 then 1 else if x < 3 then 2 else 3

/-- Five times the values of `fourCellMerging` on the cells of `fourCell`, rows for the first
e-value. -/
private def fourCellTable : Fin 4 → Fin 4 → ℕ :=
  ![![0, 0, 3, 3], ![0, 3, 3, 7], ![0, 5, 17, 17], ![5, 5, 17, 29]]

/-- An increasing merging function for independent e-values that no precise one dominates,
constant on the cells of `fourCell`. -/
private noncomputable def fourCellMerging (e : Fin 2 → ℝ≥0∞) : ℝ≥0∞ :=
  fourCellTable (fourCell (e 0)) (fourCell (e 1)) / 5

/-- `fourCell` is measurable. -/
private lemma measurable_fourCell : Measurable fourCell :=
  Measurable.ite measurableSet_Iio measurable_const <|
    Measurable.ite measurableSet_Iio measurable_const <|
      Measurable.ite measurableSet_Iio measurable_const measurable_const

/-- `fourCell` is monotone. -/
private lemma monotone_fourCell : Monotone fourCell := by
  intro x y hxy
  unfold fourCell
  split_ifs <;> first | decide | (exfalso; order)

/-- The table `fourCellTable` is monotone in both arguments. -/
private lemma fourCellTable_mono {i i' j j' : Fin 4} (hi : i ≤ i') (hj : j ≤ j') :
    fourCellTable i j ≤ fourCellTable i' j' := by
  revert i i' j j'
  decide

/-- `fourCellMerging` is increasing for the product order. -/
private lemma monotone_fourCellMerging : Monotone fourCellMerging := fun _ _ h ↦
  ENNReal.div_le_div_right
    (Nat.cast_le.2 (fourCellTable_mono (monotone_fourCell (h 0)) (monotone_fourCell (h 1)))) _

/-- The cells of the points `0, 1/2, 2, 3`. -/
private lemma fourCell_values :
    fourCell 0 = 0 ∧ fourCell 2⁻¹ = 1 ∧ fourCell 2 = 2 ∧ fourCell 3 = 3 := by
  have h2 : (2⁻¹ : ℝ≥0∞) < 2 := ENNReal.one_half_lt_one.trans ENNReal.one_lt_two
  have h3 : (2⁻¹ : ℝ≥0∞) < 3 := h2.trans (by norm_num)
  refine ⟨by simp [fourCell], by simp [fourCell, h2], ?_, ?_⟩
  · simp [fourCell, h2.not_gt, (by norm_num : (2 : ℝ≥0∞) < 3)]
  · simp [fourCell, h3.not_gt, (by norm_num : (2 : ℝ≥0∞) ≤ 3)]

/-- The real inequality behind the validity of `fourCellMerging`: the bilinear form of the table
is at most `1` on pairs of laws on `{0, 1/2, 2, 3}` with expectations at most `1`. By
`sum_mul_le_one_of_extreme`, applied twice, it suffices to check the 36 pairs of extreme laws. -/
private lemma fourCellTable_bilinear_le {P₀ P₁ P₂ P₃ Q₀ Q₁ Q₂ Q₃ : ℝ} (hP₀ : 0 ≤ P₀)
    (hP₁ : 0 ≤ P₁) (hP₂ : 0 ≤ P₂) (hP₃ : 0 ≤ P₃) (hPs : P₀ + P₁ + P₂ + P₃ = 1)
    (hPm : P₁ / 2 + 2 * P₂ + 3 * P₃ ≤ 1) (hQ₀ : 0 ≤ Q₀) (hQ₁ : 0 ≤ Q₁) (hQ₂ : 0 ≤ Q₂)
    (hQ₃ : 0 ≤ Q₃) (hQs : Q₀ + Q₁ + Q₂ + Q₃ = 1) (hQm : Q₁ / 2 + 2 * Q₂ + 3 * Q₃ ≤ 1) :
    (3 * Q₂ + 3 * Q₃) / 5 * P₀ + (3 * Q₁ + 3 * Q₂ + 7 * Q₃) / 5 * P₁ +
      (5 * Q₁ + 17 * Q₂ + 17 * Q₃) / 5 * P₂ + (5 * Q₀ + 5 * Q₁ + 17 * Q₂ + 29 * Q₃) / 5 * P₃ ≤
      1 := by
  have hQ := fun {r₀ r₁ r₂ r₃ : ℝ} ↦
    @sum_mul_le_one_of_extreme Q₀ Q₁ Q₂ Q₃ r₀ r₁ r₂ r₃ hQ₀ hQ₁ hQ₂ hQ₃ hQs hQm
  refine sum_mul_le_one_of_extreme hP₀ hP₁ hP₂ hP₃ hPs hPm ?_ ?_ ?_ ?_ ?_ ?_
  · linarith [hQ (r₀ := 0) (r₁ := 0) (r₂ := 3 / 5) (r₃ := 3 / 5) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  · linarith [hQ (r₀ := 0) (r₁ := 3 / 5) (r₂ := 3 / 5) (r₃ := 7 / 5) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  · linarith [hQ (r₀ := 0) (r₁ := 1 / 2) (r₂ := 2) (r₃ := 2) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  · linarith [hQ (r₀ := 1 / 3) (r₁ := 1 / 3) (r₂ := 23 / 15) (r₃ := 7 / 3) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  · linarith [hQ (r₀ := 0) (r₁ := 11 / 15) (r₂ := 23 / 15) (r₃ := 31 / 15) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  · linarith [hQ (r₀ := 1 / 5) (r₁ := 17 / 25) (r₂ := 29 / 25) (r₃ := 57 / 25) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]

/-- `fourCellMerging` is a merging function for independent e-values. -/
private lemma isIEMerging_fourCellMerging : IsIEMerging fourCellMerging := by
  refine isIEMerging_of_step (γ := ![0, 2⁻¹, 2, 3])
    (f := fun i j ↦ (fourCellTable i j : ℝ≥0∞) / 5) measurable_fourCell ?_
    (fun _ _ ↦ by finiteness) ?_
  · intro x
    unfold fourCell
    split_ifs with h1 h2 h3 <;> simp_all [not_lt]
  · intro P Q hP hPs hPm hQ hQs hQm
    simp [fourCellTable, Fin.sum_univ_four] at hPs hPm hQs hQm ⊢
    linarith [fourCellTable_bilinear_le (hP 0) (hP 1) (hP 2) (hP 3) hPs (by linarith) (hQ 0)
      (hQ 1) (hQ 2) (hQ 3) hQs (by linarith)]

/-- The two-point law on `ℝ≥0∞` with weight `p` on `a` and `1 - p` on `b`. -/
private noncomputable def twoPointLaw (p a b : ℝ) : Measure ℝ≥0∞ :=
  ENNReal.ofReal p • Measure.dirac (ENNReal.ofReal a) +
    ENNReal.ofReal (1 - p) • Measure.dirac (ENNReal.ofReal b)

/-- The integral against `twoPointLaw p a b`. -/
private lemma lintegral_twoPointLaw (p a b : ℝ) (f : ℝ≥0∞ → ℝ≥0∞) :
    ∫⁻ x, f x ∂twoPointLaw p a b =
      ENNReal.ofReal p * f (ENNReal.ofReal a) + ENNReal.ofReal (1 - p) * f (ENNReal.ofReal b) := by
  simp [twoPointLaw, lintegral_add_measure, lintegral_smul_measure, lintegral_dirac]

/-- `twoPointLaw p a b` is a probability measure when `0 ≤ p ≤ 1`. -/
private lemma isProbabilityMeasure_twoPointLaw {p : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) (a b : ℝ) :
    IsProbabilityMeasure (twoPointLaw p a b) := by
  constructor
  simp [twoPointLaw, ← ENNReal.ofReal_add hp₀ (sub_nonneg.2 hp₁)]

/-- The expectation of `twoPointLaw p a b` is `p * a + (1 - p) * b`. -/
private lemma lintegral_id_twoPointLaw {p a b : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) (ha : 0 ≤ a)
    (hb : 0 ≤ b) (h : p * a + (1 - p) * b = 1) : ∫⁻ x, x ∂twoPointLaw p a b = 1 := by
  rw [lintegral_twoPointLaw, ← ENNReal.ofReal_mul hp₀, ← ENNReal.ofReal_mul (sub_nonneg.2 hp₁),
    ← ENNReal.ofReal_add (mul_nonneg hp₀ ha) (mul_nonneg (sub_nonneg.2 hp₁) hb), h,
    ENNReal.ofReal_one]

/-- If `∑ wᵢ xᵢ = 1` in `ℝ≥0∞` with nonzero weights, then the `xᵢ` are finite and the same
identity holds in real numbers. -/
private lemma toReal_of_sum_four_eq_one {w₁ w₂ w₃ w₄ x₁ x₂ x₃ x₄ : ℝ≥0∞} (h₁ : w₁ ≠ 0)
    (h₂ : w₂ ≠ 0) (h₃ : w₃ ≠ 0) (h₄ : w₄ ≠ 0) (h : w₁ * x₁ + w₂ * x₂ + w₃ * x₃ + w₄ * x₄ = 1) :
    (x₁ ≠ ∞ ∧ x₂ ≠ ∞ ∧ x₃ ≠ ∞ ∧ x₄ ≠ ∞) ∧
      w₁.toReal * x₁.toReal + w₂.toReal * x₂.toReal + w₃.toReal * x₃.toReal +
        w₄.toReal * x₄.toReal = 1 := by
  have hfin : w₁ * x₁ + w₂ * x₂ + w₃ * x₃ + w₄ * x₄ ≠ ∞ := h ▸ ENNReal.one_ne_top
  simp only [ne_eq, ENNReal.add_eq_top, not_or] at hfin
  obtain ⟨⟨⟨t₁, t₂⟩, t₃⟩, t₄⟩ := hfin
  refine ⟨⟨fun hx ↦ t₁ (by rw [hx, ENNReal.mul_top h₁]),
    fun hx ↦ t₂ (by rw [hx, ENNReal.mul_top h₂]), fun hx ↦ t₃ (by rw [hx, ENNReal.mul_top h₃]),
    fun hx ↦ t₄ (by rw [hx, ENNReal.mul_top h₄])⟩, ?_⟩
  have := congrArg ENNReal.toReal h
  rwa [ENNReal.toReal_add (ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2 ⟨t₁, t₂⟩, t₃⟩) t₄,
    ENNReal.toReal_add (ENNReal.add_ne_top.2 ⟨t₁, t₂⟩) t₃, ENNReal.toReal_add t₁ t₂,
    ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_one] at this

/-- A precise merging function for two independent e-values is finite on the support of a product
of two two-point laws with mean `1`, and integrates to `1` against it, in real numbers. -/
private lemma sum_toReal_twoPointLaw_eq_one {G : (Fin 2 → ℝ≥0∞) → ℝ≥0∞}
    (hG : IsPreciseIEMerging G) {p q a b c d : ℝ} (hp₀ : 0 < p) (hp₁ : p < 1) (hq₀ : 0 < q)
    (hq₁ : q < 1) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hpm : p * a + (1 - p) * b = 1) (hqm : q * c + (1 - q) * d = 1) :
    (G ![ENNReal.ofReal a, ENNReal.ofReal c] ≠ ∞ ∧ G ![ENNReal.ofReal a, ENNReal.ofReal d] ≠ ∞ ∧
      G ![ENNReal.ofReal b, ENNReal.ofReal c] ≠ ∞ ∧ G ![ENNReal.ofReal b, ENNReal.ofReal d] ≠ ∞) ∧
    p * q * (G ![ENNReal.ofReal a, ENNReal.ofReal c]).toReal +
      p * (1 - q) * (G ![ENNReal.ofReal a, ENNReal.ofReal d]).toReal +
      (1 - p) * q * (G ![ENNReal.ofReal b, ENNReal.ofReal c]).toReal +
      (1 - p) * (1 - q) * (G ![ENNReal.ofReal b, ENNReal.ofReal d]).toReal = 1 := by
  have hμ : ∀ i, IsProbabilityMeasure (![twoPointLaw p a b, twoPointLaw q c d] i) :=
    Fin.forall_fin_two.2 ⟨isProbabilityMeasure_twoPointLaw hp₀.le hp₁.le a b,
      isProbabilityMeasure_twoPointLaw hq₀.le hq₁.le c d⟩
  have h := hG.lintegral_eq_one ![twoPointLaw p a b, twoPointLaw q c d] (Fin.forall_fin_two.2
    ⟨lintegral_id_twoPointLaw hp₀.le hp₁.le ha hb hpm,
      lintegral_id_twoPointLaw hq₀.le hq₁.le hc hd hqm⟩)
  rw [lintegral_pi_fin_two _ hG.measurable.aemeasurable] at h
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, lintegral_twoPointLaw, mul_add,
    ← mul_assoc] at h
  have wp := (ENNReal.ofReal_pos.2 hp₀).ne'
  have wp' := (ENNReal.ofReal_pos.2 (sub_pos.2 hp₁)).ne'
  have wq := (ENNReal.ofReal_pos.2 hq₀).ne'
  have wq' := (ENNReal.ofReal_pos.2 (sub_pos.2 hq₁)).ne'
  have h' := toReal_of_sum_four_eq_one (mul_ne_zero wp wq) (mul_ne_zero wp wq')
    (mul_ne_zero wp' wq) (mul_ne_zero wp' wq') (by rw [← add_assoc] at h; exact h)
  simpa [ENNReal.toReal_mul, ENNReal.toReal_ofReal, hp₀.le, hq₀.le, hp₁.le, hq₁.le] using h'

/-- `ENNReal.ofReal (1 / 2) = 2⁻¹`. -/
private lemma ofReal_one_div_two : ENNReal.ofReal (1 / 2) = 2⁻¹ := by
  rw [one_div, ENNReal.ofReal_inv_of_pos two_pos, ENNReal.ofReal_ofNat]

/-- If `G` dominates `fourCellMerging` on finite arguments and is finite at a pair of finite
arguments, its real value there is at least the value of the table. -/
private lemma div_five_le_toReal_of_fourCellMerging_le {G : (Fin 2 → ℝ≥0∞) → ℝ≥0∞}
    (hle : ∀ e : Fin 2 → ℝ≥0, fourCellMerging (fun i ↦ e i) ≤ G (fun i ↦ e i)) {x y : ℝ≥0∞}
    {i j : Fin 4} (hx : x ≠ ∞) (hy : y ≠ ∞) (hxi : fourCell x = i) (hyj : fourCell y = j)
    (hG : G ![x, y] ≠ ∞) :
    (fourCellTable i j : ℝ) / 5 ≤ (G ![x, y]).toReal := by
  have := ENNReal.toReal_mono hG (le_of_forall_nnreal hle hx hy)
  simpa [fourCellMerging, hxi, hyj, ENNReal.toReal_div] using this

/-- There is an increasing merging function for two independent e-values that no precise merging
function for independent e-values dominates on finite arguments [EVR26, Note 17]. The function is
constant on the cells `[0, 1/2), [1/2, 2), [2, 3), [3, ∞]` of each e-value, with values
`0, 0, 3/5, 3/5`; `0, 3/5, 3/5, 7/5`; `0, 1, 17/5, 17/5`; `1, 1, 17/5, 29/5` (rows for the first
e-value). -/
theorem exists_isIEMerging_monotone_not_le_isPreciseIEMerging :
    ∃ F : (Fin 2 → ℝ≥0∞) → ℝ≥0∞, IsIEMerging F ∧ Monotone F ∧
      ∀ G, IsPreciseIEMerging G → ¬ ∀ e : Fin 2 → ℝ≥0, F (fun i ↦ e i) ≤ G (fun i ↦ e i) := by
  refine ⟨fourCellMerging, isIEMerging_fourCellMerging, monotone_fourCellMerging,
    fun G hG hle ↦ ?_⟩
  -- `G` integrates to `1` against four products of two-point laws with mean `1` on
  -- `{0, 1/2, 2, 3}`; the combination `(16 E₁ - 12 E₂ + 9 E₃ + 30 E₄) / 43` is a law on eight
  -- points against which `fourCellMerging` integrates to `47/43`
  obtain ⟨⟨-, h02, -, h22⟩, E₁⟩ := sum_toReal_twoPointLaw_eq_one hG (p := 1 / 2) (q := 1 / 2)
    (a := 0) (b := 2) (c := 0) (d := 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    le_rfl zero_le_two le_rfl zero_le_two (by norm_num) (by norm_num)
  obtain ⟨-, E₂⟩ := sum_toReal_twoPointLaw_eq_one hG (p := 1 / 2) (q := 2 / 3)
    (a := 0) (b := 2) (c := 0) (d := 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    le_rfl zero_le_two le_rfl zero_le_three (by norm_num) (by norm_num)
  obtain ⟨⟨-, -, h30, h33⟩, E₃⟩ := sum_toReal_twoPointLaw_eq_one hG (p := 2 / 3) (q := 2 / 3)
    (a := 0) (b := 3) (c := 0) (d := 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    le_rfl zero_le_three le_rfl zero_le_three (by norm_num) (by norm_num)
  obtain ⟨⟨hhh, hh3, h2h, -⟩, E₄⟩ := sum_toReal_twoPointLaw_eq_one hG (p := 2 / 3) (q := 4 / 5)
    (a := 1 / 2) (b := 2) (c := 1 / 2) (d := 3) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) zero_le_two (by norm_num) zero_le_three (by norm_num) (by norm_num)
  simp only [ENNReal.ofReal_zero, ENNReal.ofReal_ofNat] at h02 h22 h30 h33
  simp only [ENNReal.ofReal_ofNat, ofReal_one_div_two] at hhh hh3 h2h
  simp only [ENNReal.ofReal_zero, ENNReal.ofReal_ofNat, ofReal_one_div_two] at E₁ E₂ E₃ E₄
  -- `G ≥ fourCellMerging` on the support of that law
  obtain ⟨c0, ch, c2, c3⟩ := fourCell_values
  have t0 : (0 : ℝ≥0∞) ≠ ∞ := by simp
  have th : (2⁻¹ : ℝ≥0∞) ≠ ∞ := by simp
  have t2 : (2 : ℝ≥0∞) ≠ ∞ := by simp
  have t3 : (3 : ℝ≥0∞) ≠ ∞ := by simp
  have k02 := div_five_le_toReal_of_fourCellMerging_le hle t0 t2 c0 c2 h02
  have k22 := div_five_le_toReal_of_fourCellMerging_le hle t2 t2 c2 c2 h22
  have k2h := div_five_le_toReal_of_fourCellMerging_le hle t2 th c2 ch h2h
  have khh := div_five_le_toReal_of_fourCellMerging_le hle th th ch ch hhh
  have kh3 := div_five_le_toReal_of_fourCellMerging_le hle th t3 ch c3 hh3
  have k33 := div_five_le_toReal_of_fourCellMerging_le hle t3 t3 c3 c3 h33
  have k30 := div_five_le_toReal_of_fourCellMerging_le hle t3 t0 c3 c0 h30
  simp only [fourCellTable, Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one,
    Nat.cast_ofNat] at k02 k22 k2h khh kh3 k33 k30
  linarith [(G ![0, 0]).toReal_nonneg]

end FinTwo

end ProbabilityTheory
